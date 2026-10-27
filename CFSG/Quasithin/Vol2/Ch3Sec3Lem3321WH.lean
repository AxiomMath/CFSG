module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321W

public section

namespace CFSG.Quasithin.H13.L3321

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.Lift CFSG.Quasithin.S152N
open CFSG.Open (pCoreOf)

namespace W3

noncomputable local instance instFintypeW3'' : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3'' : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance instDecN0''' : DecidablePred (· ∈ S152N.W3.N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

theorem mem_N0_of_comm : ∀ w : S152N.W3,
    (∀ c : S152N.W3, c ∈ S152N.W3.N0 → w * c = c * w) → w ∈ S152N.W3.N0 := by
  decide +kernel

theorem pow_three_of_mem_N0 : ∀ c : S152N.W3, c ∈ S152N.W3.N0 → c ^ 3 = 1 := by
  decide +kernel

theorem normal_isPGroup_eq_bot {N : Subgroup S152N.W3} (hN : N.Normal) (h2 : IsPGroup 2 N) :
    N = ⊥ := by
  have hdisj : ∀ x ∈ N, x ∈ S152N.W3.N0 → x = 1 := by
    intro x hxN hx0
    obtain ⟨a, ha⟩ := h2 ⟨x, hxN⟩
    have ha' : x ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    exact eq_one_of_pow_two_pow_three (b := 1) ha'
      (by rw [pow_one]; exact pow_three_of_mem_N0 x hx0)
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  refine hdisj x hx (mem_N0_of_comm x fun c hc => ?_)
  have h1 : x * c * x⁻¹ * c⁻¹ ∈ N := by
    have := hN.conj_mem x⁻¹ (N.inv_mem hx) c
    simpa [mul_assoc] using N.mul_mem hx this
  have h2' : x * c * x⁻¹ * c⁻¹ ∈ S152N.W3.N0 := by
    have := S152N.W3.N0_normal.conj_mem c hc x
    exact S152N.W3.N0.mul_mem this (S152N.W3.N0.inv_mem hc)
  have h3 := hdisj _ h1 h2'
  calc x * c = (x * c * x⁻¹ * c⁻¹) * (c * x) := by group
    _ = c * x := by rw [h3, one_mul]

end W3

section Group

variable {G : Type} [Group G] {L T : Subgroup G} {α : ↥L →* SL4}

@[expose] noncomputable def indAutFun (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) (x : ↥(Subgroup.normalizer (L : Set G))) : MulAut SL4 :=
  Classical.choose (L3316.exists_inducedAut hα hker x.2)

theorem indAutFun_spec (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (x : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L) :
    indAutFun hα hker x (α l) =
      α ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.mp x.2 l).mp l.2⟩ :=
  Classical.choose_spec (L3316.exists_inducedAut hα hker x.2) l

@[expose] noncomputable def indAut (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) : ↥(Subgroup.normalizer (L : Set G)) →* MulAut SL4 where
  toFun := indAutFun hα hker
  map_one' := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨l, rfl⟩ := hα y
    rw [indAutFun_spec, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show (1 : G) * l * 1⁻¹ = l
    group
  map_mul' x y := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨l, rfl⟩ := hα z
    rw [MulAut.mul_apply, indAutFun_spec, indAutFun_spec, indAutFun_spec]
    congr 1
    apply Subtype.ext
    show ((x : G) * y) * l * ((x : G) * y)⁻¹ = x * (y * l * (y : G)⁻¹) * (x : G)⁻¹
    group

theorem indAut_apply (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (x : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L) :
    indAut hα hker x (α l) = α ⟨x * l * x⁻¹, (Subgroup.mem_normalizer_iff.mp x.2 l).mp l.2⟩ :=
  indAutFun_spec hα hker x l

theorem indAut_of_mem (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) (l : ↥L) :
    indAut hα hker ⟨l, Subgroup.le_normalizer l.2⟩ = MulAut.conj (α l) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨l', rfl⟩ := hα y
  rw [indAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem exists_pow_mem (hT2 : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ L ⊔ T) : ∃ b : ℕ, x ^ 2 ^ b ∈ L := by
  have hx' : x ∈ ((T ⊔ L : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T L hTL] at hx'
  obtain ⟨t, ht, l, hl, rfl⟩ := hx'
  have key : ∀ m : ℕ, ∃ l' ∈ L, (t * l) ^ m = t ^ m * l' := by
    intro m
    induction m with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', e⟩ := ih
      have hc : t⁻¹ * l' * t ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem ht)) l').mp hl'
        simpa using this
      refine ⟨(t⁻¹ * l' * t) * l, L.mul_mem hc hl, ?_⟩
      rw [pow_succ, e, pow_succ]
      group
  obtain ⟨b, hb⟩ := hT2 ⟨t, ht⟩
  have hb' : t ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  obtain ⟨l', hl', e⟩ := key (2 ^ b)
  refine ⟨b, ?_⟩
  rw [e, hb', one_mul]
  exact hl'

theorem exists_pow_eq_one_of_indAut [Finite G] (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) (hT2 : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (x : ↥(Subgroup.normalizer (L : Set G)))
    (hxLT : (x : G) ∈ L ⊔ T) (hx : indAut hα hker x = 1) : ∃ n : ℕ, (x : G) ^ 2 ^ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := exists_pow_mem hT2 hTL hxLT
  have h1 : indAut hα hker (x ^ 2 ^ b) = 1 := by rw [map_pow, hx, one_pow]
  have h2 : (x ^ 2 ^ b : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨(⟨(x : G) ^ 2 ^ b, hb⟩ : ↥L), Subgroup.le_normalizer hb⟩ := Subtype.ext (by simp)
  rw [h2, indAut_of_mem] at h1
  have h3 : α ⟨(x : G) ^ 2 ^ b, hb⟩ = 1 := by
    apply SteinbergCD.injective_conj_binarySL 4
    rw [h1, map_one]
  have h4 : (⟨(x : G) ^ 2 ^ b, hb⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rw [← hker]
    exact h3
  obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, h4⟩
  refine ⟨b + c, ?_⟩
  have := congrArg (fun z : ↥(CFSG.pCore 2 ↥L) => ((z : ↥L) : G)) hc
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  rw [pow_add, pow_mul, this]

end Group

section Wreath

variable {G : Type} [Group G] {L T : Subgroup G} {α : ↥L →* SL4}

theorem map_Ut_indAut (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hU : ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4)
    {t : G} (ht : t ∈ T) :
    (FLc.Ut 4).map (indAut hα hker ⟨t, hTL ht⟩).toMonoidHom = FLc.Ut 4 := by
  have key : ∀ t (ht : t ∈ T), ∀ u ∈ FLc.Ut 4, indAut hα hker ⟨t, hTL ht⟩ u ∈ FLc.Ut 4 := by
    intro t ht u hu
    rw [← hU] at hu ⊢
    obtain ⟨s, hs, rfl⟩ := hu
    have hs' : (s : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 hs
    rw [indAut_apply]
    refine ⟨_, Subgroup.mem_subgroupOf.2 ⟨T.mul_mem (T.mul_mem ht hs'.1) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp (hTL ht) s).mp hs'.2⟩, rfl⟩
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact key t ht u hu
  · intro u hu
    refine ⟨indAut hα hker ⟨t⁻¹, hTL (T.inv_mem ht)⟩ u, key t⁻¹ (T.inv_mem ht) u hu, ?_⟩
    show (indAut hα hker ⟨t, hTL ht⟩ * indAut hα hker ⟨t⁻¹, hTL (T.inv_mem ht)⟩) u = u
    rw [← map_mul]
    have : (⟨t, hTL ht⟩ * ⟨t⁻¹, hTL (T.inv_mem ht)⟩ : ↥(Subgroup.normalizer (L : Set G))) = 1 :=
      Subtype.ext (mul_inv_cancel t)
    rw [this, map_one, MulAut.one_apply]

theorem nonempty_wreath [Finite G] (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hU : ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4) (hout : ¬ InducesInnerOn T L) :
    Nonempty (↥(L3316.liftPre α P2 ⊔ T) ⧸ CFSG.pCore 2 ↥(L3316.liftPre α P2 ⊔ T) ≃*
      ↥wreathS3Z2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := L3316.liftPre α P2 with hPdef
  set H := P ⊔ T with hHdef
  have hPL : P ≤ L := L3316.liftPre_le α P2
  have hHN : H ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hPL.trans Subgroup.le_normalizer) hTL
  have hHLT : H ≤ L ⊔ T := sup_le_sup_right hPL T
  set Φ : ↥H →* MulAut SL4 := (indAut hα hker).comp (Subgroup.inclusion hHN) with hΦ
  have hrange : ∀ h : ↥H, Φ h ∈ xiHom.range := by
    let K : Subgroup G := (xiHom.range.comap (indAut hα hker)).map
      (Subgroup.normalizer (L : Set G)).subtype
    have hPK : P ≤ K := by
      rintro _ ⟨l, hl, rfl⟩
      refine ⟨⟨l, Subgroup.le_normalizer l.2⟩, ?_, rfl⟩
      show indAut hα hker ⟨l, Subgroup.le_normalizer l.2⟩ ∈ xiHom.range
      rw [indAut_of_mem]
      refine ⟨⟨⟨α l, hl⟩, 1⟩, ?_⟩
      rw [xiHom_mk, map_one, mul_one]
    have hTK : T ≤ K := by
      intro t ht
      refine ⟨⟨t, hTL ht⟩, ?_, rfl⟩
      obtain ⟨u, hu, k, hk⟩ := exists_xiHom_of_map_Ut _ (map_Ut_indAut hα hker hTL hU ht)
      exact ⟨_, hk.symm⟩
    intro h
    obtain ⟨y, hy, hyh⟩ := (sup_le hPK hTK) h.2
    have e : (y : ↥(Subgroup.normalizer (L : Set G))) = Subgroup.inclusion hHN h :=
      Subtype.ext hyh
    show indAut hα hker (Subgroup.inclusion hHN h) ∈ xiHom.range
    rw [← e]
    exact hy
  set e := MonoidHom.ofInjective xiHom_injective with he
  set ψ : ↥H →* W3 :=
    chiHom.comp (e.symm.toMonoidHom.comp (Φ.codRestrict xiHom.range hrange)) with hψ
  have hψ_eq : ∀ (h : ↥H) (gk : Pgam), Φ h = xiHom gk → ψ h = chiHom gk := by
    intro h gk hgk
    have h1 : e gk = Φ.codRestrict xiHom.range hrange h := Subtype.ext hgk.symm
    show chiHom (e.symm (Φ.codRestrict xiHom.range hrange h)) = chiHom gk
    rw [← h1, MulEquiv.symm_apply_apply]
  have hT1 : ∃ (t : G) (ht : t ∈ T) (u : SL4) (hu : u ∈ FLc.Ut 4),
      indAut hα hker ⟨t, hTL ht⟩ = xiHom ⟨⟨u, Ut_le_P2 hu⟩, Multiplicative.ofAdd 1⟩ := by
    by_contra hno
    apply hout
    intro t ht
    obtain ⟨u, hu, k, hk⟩ := exists_xiHom_of_map_Ut _ (map_Ut_indAut hα hker hTL hU ht)
    rcases mult_z2_cases k with rfl | rfl
    · rw [xiHom_mk, map_one, mul_one] at hk
      obtain ⟨y, hy⟩ := hα u
      refine ⟨y, y.2, fun x hx => ?_⟩
      have hxt := (Subgroup.mem_normalizer_iff.mp (hTL ht) x).mp hx
      have h1 : α ⟨t * x * t⁻¹, hxt⟩ = α (y * ⟨x, hx⟩ * y⁻¹) := by
        have h2 := indAut_apply hα hker ⟨t, hTL ht⟩ ⟨x, hx⟩
        rw [hk, MulAut.conj_apply] at h2
        rw [map_mul, map_mul, map_inv, hy]
        exact h2.symm
      have h3 : (⟨t * x * t⁻¹, hxt⟩ : ↥L) * (y * ⟨x, hx⟩ * y⁻¹)⁻¹ ∈ CFSG.pCore 2 ↥L := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
      exact (Lem3328.mem_pCore_iff _).1 h3
    · exact absurd ⟨t, ht, u, hu, hk⟩ hno
  obtain ⟨t₀, ht₀, u₀, hu₀, hk₀⟩ := hT1
  have ht₀H : t₀ ∈ H := Subgroup.mem_sup_right ht₀
  have hψt₀ : ψ ⟨t₀, ht₀H⟩ = chiHom ⟨⟨u₀, Ut_le_P2 hu₀⟩, Multiplicative.ofAdd 1⟩ :=
    hψ_eq _ _ hk₀
  have hbase : ∀ w : W3, w.right = 1 → ∃ h : ↥H, ψ h = w := by
    intro w hw
    obtain ⟨⟨g, k⟩, hgk⟩ := chiHom_surjective w
    have hk : k = 1 := by
      have h1 : (baseW (betaB g) * RegularWreathProduct.inl k).right = 1 := by
        rw [← chiHom_mk, hgk, hw]
      rwa [RegularWreathProduct.mul_right, RegularWreathProduct.right_inl,
        show (baseW (betaB g)).right = 1 from rfl, one_mul] at h1
    subst hk
    obtain ⟨l, hl⟩ := hα (g : SL4)
    have hlP : (l : G) ∈ P := ⟨l, show α l ∈ P2 by rw [hl]; exact g.2, rfl⟩
    refine ⟨⟨l, Subgroup.mem_sup_left hlP⟩, ?_⟩
    rw [← hgk]
    refine hψ_eq _ _ ?_
    show indAut hα hker ⟨l, _⟩ = _
    rw [indAut_of_mem, xiHom_mk, map_one, mul_one, hl]
  have hψs : Function.Surjective ψ := by
    intro w
    rcases mult_z2_cases w.right with hw | hw
    · exact hbase w hw
    · have hr : (ψ ⟨t₀, ht₀H⟩).right = Multiplicative.ofAdd 1 := by
        rw [hψt₀, chiHom_mk, RegularWreathProduct.mul_right, RegularWreathProduct.right_inl,
          show (baseW (betaB ⟨u₀, Ut_le_P2 hu₀⟩)).right = 1 from rfl, one_mul]
      obtain ⟨h, hh⟩ := hbase (w * (ψ ⟨t₀, ht₀H⟩)⁻¹) (by
        rw [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, hr, hw,
          mul_inv_cancel])
      exact ⟨h * ⟨t₀, ht₀H⟩, by rw [map_mul, hh, inv_mul_cancel_right]⟩
  have hker2 : IsPGroup 2 ψ.ker := by
    rintro ⟨h, hh⟩
    have hh' : ψ h = 1 := hh
    obtain ⟨⟨g, k⟩, hgk⟩ : ∃ gk : Pgam, e gk = Φ.codRestrict xiHom.range hrange h :=
      ⟨_, e.apply_symm_apply _⟩
    have hxi : xiHom ⟨g, k⟩ = Φ h := by
      have h1 : ((e ⟨g, k⟩ : ↥xiHom.range) : MulAut SL4) =
          ((Φ.codRestrict xiHom.range hrange h : ↥xiHom.range) : MulAut SL4) :=
        congrArg Subtype.val hgk
      rw [he, MonoidHom.ofInjective_apply] at h1
      exact h1
    have hchi : chiHom ⟨g, k⟩ = 1 := by rw [← hψ_eq h _ hxi.symm, hh']
    obtain ⟨hk1, hgU⟩ := chiHom_eq_one hchi
    have hΦh : Φ h = MulAut.conj (g : SL4) := by rw [← hxi, xiHom_mk, hk1, map_one, mul_one]
    obtain ⟨a, ha⟩ := (SzN2.isSylowTwoOf_unitriangular (K := ZMod 2) (n := 4)
      (by norm_num)).2.1 ⟨g, hgU⟩
    have ha' : (g : SL4) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hΦ2 : indAut hα hker (Subgroup.inclusion hHN (h ^ 2 ^ a)) = 1 := by
      rw [map_pow, map_pow]
      show (Φ h) ^ 2 ^ a = 1
      rw [hΦh, ← map_pow, ha', map_one]
    obtain ⟨b, hb⟩ := exists_pow_eq_one_of_indAut hα hker hT2 hTL _ (hHLT (h ^ 2 ^ a).2) hΦ2
    refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
    have hb' : ((h : G) ^ 2 ^ a) ^ 2 ^ b = 1 := hb
    show (h : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul, hb']
  have hle1 : ψ.ker ≤ CFSG.pCore 2 ↥H := le_sSup ⟨MonoidHom.normal_ker ψ, hker2⟩
  have hle2 : CFSG.pCore 2 ↥H ≤ ψ.ker := by
    have hN : ((CFSG.pCore 2 ↥H).map ψ).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥H)).map ψ hψs
    have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥H).map ψ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map ψ
    have hbot := W3.normal_isPGroup_eq_bot hN h2
    intro x hx
    rw [MonoidHom.mem_ker]
    have : ψ x ∈ (CFSG.pCore 2 ↥H).map ψ := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hkeq : ψ.ker = CFSG.pCore 2 ↥H := le_antisymm hle1 hle2
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal (p := 2) (G := ↥H)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkeq.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).trans Wreath.wreathEquiv)⟩

end Wreath

end CFSG.Quasithin.H13.L3321
