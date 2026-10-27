module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptMod
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3319
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {t : G}

namespace Sett

variable (e : Sett T M L t)
include e

theorem isPSL_autOn_L2 (h : IsPSL 3 2 1 ↥(autOn L (vPlus L T))) :
    IsPSL 3 2 1 ↥(autOn (CFSG.conjugate L t) (vPlus L T)) := by
  have h1 := e.conjSub_tinv
  set g := conjOf (vPlus L T) (L ⊔ T) e.hX ⟨t⁻¹, e.tinv_mem⟩ with hg
  have e1 : ↥(autOn L (vPlus L T)) ≃* ↥(conjSub g (autOn L (vPlus L T))) :=
    Subgroup.equivMapOfInjective (autOn L (vPlus L T)) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
  have e2 : ↥(conjSub g (autOn L (vPlus L T))) ≃* ↥(autOn (CFSG.conjugate L t) (vPlus L T)) :=
    MulEquiv.subgroupCongr h1
  exact IsPSL.of_mulEquiv (e1.trans e2) h

theorem false_of_commutator_le (hPSL : IsPSL 3 2 1 ↥(autOn L (vPlus L T)))
    (hI : ⁅vPlus L T, L⁆ ⊓ ⁅vPlus L T, CFSG.conjugate L t⁆ = ⊥)
    {K₀ : Subgroup G} {e₀ y : G}
    (hL2e : CFSG.conjugate L t ≤ Subgroup.centralizer ({e₀} : Set G))
    (hyK : y ∈ K₀) (hyM : y ∈ mPlus L T)
    (hy2 : y ∉ Subgroup.centralizer ((⁅vPlus L T, CFSG.conjugate L t⁆ : Subgroup G) : Set G))
    (hcomm : ⁅K₀, CFSG.conjugate L t⁆ ≤ pCoreOf 2 (Subgroup.centralizer ({e₀} : Set G))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := vPlus L T with hV
  set L2 := CFSG.conjugate L t with hL2
  set ρ := conjOf V (L ⊔ T) e.hX with hρ
  have hL2X : L2 ≤ L ⊔ T := e.L2_le
  have hL2M : L2 ≤ mPlus L T := by rw [e.hM]; exact le_sup_right
  have hMX : mPlus L T ≤ L ⊔ T := by rw [e.hM]; exact sup_le le_sup_left e.L2_le
  have hAPSL := e.isPSL_autOn_L2 hPSL
  have hAsimple : IsSimpleGroup ↥(autOn L2 V) :=
    SBc11.isSimpleGroup_of_list (Or.inl hAPSL)
  have hAcard : Nat.card ↥(autOn L2 V) = 168 := SBc11.card_of_isPSL_three_two hAPSL
  have hAcenter : Subgroup.center ↥(autOn L2 V) = ⊥ := SBc11.center_eq_bot_of_list (Or.inl hAPSL)
  set O := pCoreOf 2 (Subgroup.centralizer ({e₀} : Set G)) with hO
  set R := O ⊓ mPlus L T with hR
  have hR2 : IsPGroup 2 ↥R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_left
  have hRX : R ≤ L ⊔ T := inf_le_right.trans hMX
  have hmR : ∀ m ∈ L2, m ∈ Subgroup.normalizer (R : Set G) := by
    intro m hm
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hL2e hm)
    · exact Subgroup.le_normalizer (hL2M hm)
  have hRbar2 : IsPGroup 2 ↥(autOn R V) := by
    rw [← map_conjOf e.hX hRX]
    exact (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm).map ρ
  set A := autOn L2 V with hA
  set N := autOn R V ⊓ A with hN
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (N : Set (MulAut ↥V)) := by
    intro a ha
    obtain ⟨m, hmL2, rfl⟩ := exists_conjOf_eq e.hX hL2X ha
    have h1 : conjSub (ρ m) (autOn R V) = autOn R V := by
      rw [conjSub_autOn e.hX m R]
      have := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hmR (m : G) hmL2)
      exact congrArg (fun K => autOn K V) this
    have h2 : conjSub (ρ m) A = A := by
      rw [hA, conjSub_autOn e.hX m L2]
      have := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer (show (m : G) ∈ L2 from hmL2))
      exact congrArg (fun K => autOn K V) this
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub (ρ m) N = N
    have : conjSub (ρ m) N = conjSub (ρ m) (autOn R V) ⊓ conjSub (ρ m) A :=
      Subgroup.map_inf _ _ _ (MulAut.conj (ρ m)).injective
    rw [this, h1, h2]
  have hNn : (N.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hAN
  have hNbot : N = ⊥ := by
    rcases hAsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
    · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
    · exfalso
      have hAN' : A ≤ N := Subgroup.subgroupOf_eq_top.mp h
      have h2 : IsPGroup 2 ↥A := hRbar2.to_le (hAN'.trans inf_le_left)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [hAcard] at hn
      have h1 : n ≤ 7 := by
        by_contra h1
        have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [← hn] at this
        norm_num at this
      interval_cases n <;> norm_num at hn
  have hyM' : y ∈ ((mPlus L T : Subgroup G) : Set G) := hyM
  rw [e.coe_mPlus] at hyM'
  obtain ⟨l₂, hl₂, l, hl, hyll⟩ := hyM'
  have hyll' : y = l₂ * l := hyll.symm
  have hl₂X : l₂ ∈ L ⊔ T := hL2X hl₂
  have hlX : l ∈ L ⊔ T := Subgroup.mem_sup_left hl
  have hyX : y ∈ L ⊔ T := hMX hyM
  set b := ρ ⟨l₂, hl₂X⟩ with hb
  set a := ρ ⟨l, hlX⟩ with ha
  have hbA : b ∈ A := conjOf_mem_autOn e.hX hl₂
  have haL : a ∈ autOn L V := conjOf_mem_autOn e.hX hl
  have hcom : ∀ c ∈ A, ⁅b, c⁆ = 1 := by
    intro c hc
    obtain ⟨m, hmL2, rfl⟩ := exists_conjOf_eq e.hX hL2X hc
    set m' : ↥(L ⊔ T) := m with hm'
    have hmK : (m : G) ∈ L2 := hmL2
    have hcomm1 : ⁅y, (m : G)⁆ ∈ ⁅K₀, L2⁆ := Subgroup.commutator_mem_commutator hyK hmK
    have hyMm : ⁅y, (m : G)⁆ ∈ mPlus L T :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyM (hL2M hmK))
        ((mPlus L T).inv_mem hyM)) ((mPlus L T).inv_mem (hL2M hmK))
    have hRm : ⁅y, (m : G)⁆ ∈ R := ⟨hcomm hcomm1, hyMm⟩
    set y' : ↥(L ⊔ T) := ⟨y, hyX⟩ with hy'
    have hco : ((⁅y', m'⁆ : ↥(L ⊔ T)) : G) = ⁅y, (m : G)⁆ := rfl
    have hcr : ρ ⁅y', m'⁆ ∈ autOn R V :=
      conjOf_mem_autOn e.hX (x := ⁅y', m'⁆) (hco ▸ hRm)
    have hy'e : y' = ⟨l₂, hl₂X⟩ * ⟨l, hlX⟩ := Subtype.ext hyll'
    have hrho : ρ ⁅y', m'⁆ = ⁅b * a, ρ m'⁆ := by
      rw [commutatorElement_def, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
        map_inv, hy'e, map_mul]
    have hcA : ρ m' ∈ A := conjOf_mem_autOn e.hX hmL2
    have hac : a * ρ m' = ρ m' * a := e.comm a haL _ hcA
    have hcomm2 : ⁅b * a, ρ m'⁆ = ⁅b, ρ m'⁆ := by
      simp only [commutatorElement_def]
      calc b * a * ρ m' * (b * a)⁻¹ * (ρ m')⁻¹
          = b * (a * ρ m') * a⁻¹ * b⁻¹ * (ρ m')⁻¹ := by group
        _ = b * (ρ m' * a) * a⁻¹ * b⁻¹ * (ρ m')⁻¹ := by rw [hac]
        _ = b * ρ m' * b⁻¹ * (ρ m')⁻¹ := by group
    have hbc : ⁅b, ρ m'⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem hbA hcA) (A.inv_mem hbA)) (A.inv_mem hcA)
    have hbN : ⁅b, ρ m'⁆ ∈ N := by
      refine ⟨?_, hbc⟩
      rw [← hcomm2, ← hrho]
      exact hcr
    rw [hNbot, Subgroup.mem_bot] at hbN
    exact hbN
  have hbcen : (⟨b, hbA⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hcom g.1 g.2
    rw [commutatorElement_def] at h1
    apply Subtype.ext
    show g.1 * b = b * g.1
    have h2 : b * g.1 = g.1 * b := by
      calc b * g.1 = (b * g.1 * b⁻¹ * g.1⁻¹) * (g.1 * b) := by group
        _ = g.1 * b := by rw [h1, one_mul]
    exact h2.symm
  rw [hAcenter, Subgroup.mem_bot] at hbcen
  have hb1 : b = 1 := congrArg Subtype.val hbcen
  have hl₂C : l₂ ∈ Subgroup.centralizer (V : Set G) :=
    (conjOf_eq_one_iff e.hX ⟨l₂, hl₂X⟩).mp hb1
  apply hy2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvV : v ∈ V := commutator_le_of_le_normalizer (fun x hx => e.hX (e.L2_le hx)) hv
  have h1 : v * l₂ = l₂ * v := Subgroup.mem_centralizer_iff.mp hl₂C v hvV
  have h2 : l * v = v * l := e.L_centralizes_V2 hI hl hv
  rw [hyll']
  calc v * (l₂ * l) = (v * l₂) * l := by group
    _ = (l₂ * v) * l := by rw [h1]
    _ = l₂ * (v * l) := by group
    _ = l₂ * (l * v) := by rw [h2]
    _ = l₂ * l * v := by group

theorem a38Types_L2 : A38Types (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) := by
  rcases lemma_1_2_1_three e.s.qtke e.s.simple e.s.nonabelian (a37ForSQTK_of_cat e.h37)
      (a38ForSQTK_of_cat e.h38) e.s.pCoreOf_ne_bot e.L2_mem_cComp with hL | ⟨-, h⟩
  · exfalso
    have h1 : L ⊔ T ≤ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer e.L2_le).mp hL
    have ht : t ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G) :=
      h1 (Subgroup.mem_sup_right e.ht)
    obtain ⟨-, h2⟩ := e.swap_conj e.ht e.htn
    apply e.L_ne_L2
    exact h2.symm.trans (A38.map_conj_eq_iff.mpr ht)
  · exact h

theorem not_isPGroup_autOn_L2 (hPSL : IsPSL 3 2 1 ↥(autOn L (vPlus L T))) :
    ¬ IsPGroup 2 ↥(autOn (CFSG.conjugate L t) (vPlus L T)) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  rw [SBc11.card_of_isPSL_three_two (e.isPSL_autOn_L2 hPSL)] at hn
  have h1 : n ≤ 7 := by
    by_contra h1
    have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at this
    norm_num at this
  interval_cases n <;> norm_num at hn

theorem isPSL_modO2_L2 (hPSL : IsPSL 3 2 1 ↥(autOn L (vPlus L T))) :
    IsPSL 3 2 1 (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := vPlus L T with hV
  set L2 := CFSG.conjugate L t with hL2
  have hL2V : L2 ≤ Subgroup.normalizer (V : Set G) := fun x hx => e.hX (e.L2_le hx)
  set π := conjOf V L2 hL2V with hπ
  have hAPSL := e.isPSL_autOn_L2 hPSL
  have hAsimple : IsSimpleGroup ↥(autOn L2 V) := SBc11.isSimpleGroup_of_list (Or.inl hAPSL)
  have hnotP := e.not_isPGroup_autOn_L2 hPSL
  have hker : π.ker = CFSG.pCore 2 ↥L2 := by
    apply le_antisymm
    · intro x hx
      have hxC : (x : G) ∈ Subgroup.centralizer (V : Set G) := (conjOf_eq_one_iff hL2V x).mp hx
      exact inf_centralizer_le_pCore hL2V e.a38Types_L2 hnotP x.2 hxC
    · intro x hx
      have hrange : π.range = autOn L2 V := range_conjOf hL2V
      have hsimple : IsSimpleGroup ↥π.range := by
        rw [hrange]; exact hAsimple
      set N' := (CFSG.pCore 2 ↥L2).map π.rangeRestrict with hN'
      have hN'n : N'.Normal := (CFSG.pCore_normal (p := 2) (G := ↥L2)).map _ π.rangeRestrict_surjective
      have hN'p : IsPGroup 2 ↥N' := (CFSG.pCore_isPGroup (p := 2) (G := ↥L2)).map _
      haveI := hN'n
      rcases hsimple.eq_bot_or_eq_top_of_normal N' with h | h
      · have : π.rangeRestrict x ∈ N' := Subgroup.mem_map_of_mem _ hx
        rw [h, Subgroup.mem_bot] at this
        exact (MonoidHom.mem_ker).mpr (by simpa using congrArg Subtype.val this)
      · exfalso
        apply hnotP
        have h2 : IsPGroup 2 ↥π.range := by
          have : IsPGroup 2 ↥(⊤ : Subgroup ↥π.range) := h ▸ hN'p
          exact (IsPGroup.of_equiv this Subgroup.topEquiv)
        rw [← hrange]
        exact h2
  have e1 : ↥L2 ⧸ π.ker ≃* ↥π.range := QuotientGroup.quotientKerEquivRange π
  have e2 : ↥L2 ⧸ CFSG.pCore 2 ↥L2 ≃* ↥π.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans e1
  have e3 : ↥π.range ≃* ↥(autOn L2 V) := MulEquiv.subgroupCongr (range_conjOf hL2V)
  exact IsPSL.of_mulEquiv (e2.trans e3).symm hAPSL

end Sett

end CFSG.Quasithin.H13.Ins314
