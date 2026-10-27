module

public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.Vol2.Ch1Local

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement

namespace Lem3228

variable {G : Type} [Group G]

omit [Group G] in
theorem le_normalizer_of_conj_le' [Group G] {H K : Subgroup G}
    (hn : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K) : H ≤ Subgroup.normalizer (K : Set G) :=
  fun x hx => Subgroup.mem_normalizer_iff.mpr fun k =>
    ⟨fun hk => hn x hx k hk, fun hk => by
      have := hn x⁻¹ (H.inv_mem hx) _ hk
      simpa [mul_assoc] using this⟩

theorem normal_subgroupOf_of_commute {C J : Subgroup G}
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a) : (C.subgroupOf J).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have : g * n * g⁻¹ = n := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hJ g g.2 n n.2, mul_inv_cancel_right]
  rw [this]
  exact hn

theorem conj_mem_of_normal {C E : Subgroup G} (hCn : (C.subgroupOf E).Normal) {c g : G}
    (hc : c ∈ C) (hcE : c ∈ E) (hg : g ∈ E) : g * c * g⁻¹ ∈ C := by
  have := hCn.conj_mem ⟨c, hcE⟩ (Subgroup.mem_subgroupOf.mpr hc) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.mp this

variable [Finite G]

theorem exists_fixed_mod {E C : Subgroup G} (hCn : (C.subgroupOf E).Normal)
    (hE2 : IsPGroup 2 ↥E) (hlt : ¬ E ≤ C) {x : G}
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) (hxC : x ∈ Subgroup.normalizer (C : Set G))
    {k : ℕ} (hxk : ∀ e ∈ E, x ^ 2 ^ k * e * (x ^ 2 ^ k)⁻¹ * e⁻¹ ∈ C) :
    ∃ e ∈ E, e ∉ C ∧ x * e * x⁻¹ * e⁻¹ ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEx : E.map (MulAut.conj x).toMonoidHom = E := A38.map_conj_eq_iff.mpr hxE
  let φ : ↥E ≃* ↥E := ((MulAut.conj x).subgroupMap E).trans (MulEquiv.subgroupCongr hEx)
  have hφ : ∀ e : ↥E, (φ e : G) = x * e * x⁻¹ := fun e => rfl
  have hCφ : (C.subgroupOf E).map φ.toMonoidHom = C.subgroupOf E := by
    ext e
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [hφ]
      exact (Subgroup.mem_normalizer_iff.mp hxC f).mp hf
    · intro he
      refine ⟨φ.symm e, ?_, φ.apply_symm_apply e⟩
      have h1 : x * ((φ.symm e : ↥E) : G) * x⁻¹ = e := by rw [← hφ, φ.apply_symm_apply]
      have h2 : ((φ.symm e : ↥E) : G) = x⁻¹ * e * x := by rw [← h1]; group
      rw [h2]
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxC) (e : G)).mp he
      simpa using this
  let σ : MulAut (↥E ⧸ C.subgroupOf E) := QuotientGroup.congr _ _ φ hCφ
  have hσ : ∀ e : ↥E, σ (e : ↥E ⧸ C.subgroupOf E) = ((φ e : ↥E) : ↥E ⧸ C.subgroupOf E) :=
    fun e => rfl
  have hσn : ∀ (n : ℕ) (e : ↥E), ∃ f : ↥E, (f : G) = x ^ n * e * (x ^ n)⁻¹ ∧
      (σ ^ n) (e : ↥E ⧸ C.subgroupOf E) = (f : ↥E ⧸ C.subgroupOf E) := by
    intro n
    induction n with
    | zero => exact fun e => ⟨e, by simp, by simp⟩
    | succ n ih =>
      intro e
      obtain ⟨f, hf, hσf⟩ := ih (φ e)
      refine ⟨f, ?_, ?_⟩
      · rw [hf, hφ]; group
      · rw [pow_succ, MulAut.mul_apply, hσ, hσf]
  have hσk : σ ^ 2 ^ k = 1 := by
    apply MulEquiv.ext
    intro q
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨f, hf, hσf⟩ := hσn (2 ^ k) e
    rw [MulAut.one_apply]
    erw [hσf]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hxk e e.2
    rw [← hf] at h1
    have h2 : (e : G) * (f : G)⁻¹ ∈ C := by
      have := C.inv_mem h1
      simpa using this
    have h3 := conj_mem_of_normal hCn h2 (E.mul_mem e.2 (E.inv_mem f.2)) (E.inv_mem e.2)
    have e2 : ((f⁻¹ * e : ↥E) : G) = (e : G)⁻¹ * ((e : G) * (f : G)⁻¹) * (e : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e2]
    exact h3
  have hQ2 : IsPGroup 2 (↥E ⧸ C.subgroupOf E) := hE2.to_quotient _
  obtain ⟨m, hm⟩ := hQ2.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    apply hlt
    intro y hy
    have : (⟨y, hy⟩ : ↥E) ∈ C.subgroupOf E := by
      rw [← QuotientGroup.eq_one_iff]
      have : Subsingleton (↥E ⧸ C.subgroupOf E) := (Nat.card_eq_one_iff_unique.mp hm).1
      exact Subsingleton.elim _ _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨q, hq1, hqσ⟩ := exists_ne_one_fixed (by rw [hm]; exact dvd_pow_self 2 hm0) σ hσk
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨e, e.2, fun he => hq1 ((QuotientGroup.eq_one_iff _).mpr
    (Subgroup.mem_subgroupOf.mpr he)), ?_⟩
  rw [hσ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hqσ
  have h1 : ((φ e : ↥E) : G)⁻¹ * e ∈ C := by simpa using hqσ
  rw [hφ] at h1
  have h2 : (e : G)⁻¹ * (x * e * x⁻¹) ∈ C := by
    have := C.inv_mem h1
    simpa [mul_assoc] using this
  have h3 := conj_mem_of_normal hCn h2
    (E.mul_mem (E.inv_mem e.2) ((Subgroup.mem_normalizer_iff.mp hxE e).mp e.2)) e.2
  have e3 : (e : G) * ((e : G)⁻¹ * (x * e * x⁻¹)) * (e : G)⁻¹ = x * e * x⁻¹ * (e : G)⁻¹ := by
    group
  rw [e3] at h3
  exact h3

theorem le_centralizer_of_two {L K V : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hperf : ⁅L, L⁆ = L)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) (hKL : K ≤ L)
    (hLK : L ≤ Subgroup.normalizer (K : Set G))
    (h2 : ∀ k ∈ K, ∃ e : ℕ, k ^ 2 ^ e ∈ Subgroup.centralizer (V : Set G)) :
    K ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPO : ∀ p : ↥L, p ∈ CFSG.pCore 2 ↥L → (p : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro p hp
    refine hO ⟨p, ?_, rfl⟩
    exact hp
  have hKn : (K.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr hLK
  have hKn' : ((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    hKn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      (B1Red.isQuasisimple_to_open hq)
      ((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with hc | ht
  · intro k hk
    set kL : ↥L := ⟨k, hKL hk⟩ with hkL
    set y := QuotientGroup.mk' (CFSG.pCore 2 ↥L) kL with hy
    have hz : y ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
      hc ⟨kL, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    have hyb : (y ^ b) ^ 2 ^ a = 1 := by
      rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
    have hzb : Subgroup.zpowers (y ^ b) ≤ CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) := by
      refine CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup ⟨fun n hn g => ?_⟩
        (isPGroup_zpowers_of_pow hyb)
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hcz : (y ^ b) ^ i ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
        Subgroup.zpow_mem _ (Subgroup.pow_mem _ hz b) i
      rw [Subgroup.mem_center_iff.mp hcz g, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ i
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hzb
    have hyb1 : y ^ b = 1 := Subgroup.mem_bot.mp (hzb (Subgroup.mem_zpowers _))
    have hkb : k ^ b ∈ Subgroup.centralizer (V : Set G) := by
      have : kL ^ b ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
        exact hyb1
      have := hPO _ this
      simpa [hkL] using this
    obtain ⟨e, he⟩ := h2 k hk
    have hcop : Nat.Coprime b (2 ^ e) :=
      Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hb)
    have hgcd := Nat.gcd_eq_gcd_ab b (2 ^ e)
    rw [hcop, Nat.cast_one] at hgcd
    have hk1 : k = (k ^ b) ^ (Nat.gcdA b (2 ^ e)) * (k ^ 2 ^ e) ^ (Nat.gcdB b (2 ^ e)) := by
      rw [← zpow_natCast, ← zpow_natCast (k) (2 ^ e), ← zpow_mul, ← zpow_mul, ← zpow_add,
        ← hgcd, zpow_one]
    rw [hk1]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hkb _) (Subgroup.zpow_mem _ he _)
  ·
    have hn : ((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr fun l hl =>
        mem_normalizer_inf (B2F.normalizer_le_normalizer_centralizer V (hLV hl))
          (Subgroup.le_normalizer hl)
    have hp : IsPGroup 2 (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) := by
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have hl : QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈
          (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := ht ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkl⟩ := hl
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkl
      obtain ⟨e, he⟩ := h2 k (Subgroup.mem_subgroupOf.mp hk)
      refine ⟨e, ?_⟩
      have hq' : (l : ↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) =
          (k : ↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have := Subgroup.inv_mem _ (hPO _ hkl)
        simpa using this
      rw [hq', ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using he
    exact hKL.trans (le_of_isPGroup_quotient hperf hp)

theorem conjClosure_le_normalizer_of_cComp
    (hK : QuasithinUnique.quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {T L : Subgroup G}
    (hH : pCoreOf 2 (L ⊔ T) ≠ ⊥) (hL : L ∈ cComp (L ⊔ T)) :
    conjClosure L T ≤ Subgroup.normalizer (L : Set G) := by
  refine conjClosure_le fun t ht l hl => ?_
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ cComp (L ⊔ T) :=
    map_conj_mem_cComp hL (Subgroup.mem_sup_right ht)
  have hmem : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := ⟨l, hl, rfl⟩
  by_cases heq : L.map (MulAut.conj t).toMonoidHom = L
  · rw [heq] at hmem
    exact Subgroup.le_normalizer hmem
  · obtain ⟨h1, -⟩ := lemma_1_2_1_two hK hs hnab
      (a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved) hH hLt hL heq
    refine le_normalizer_of_conj_le' (fun y hy x hx => ?_) hmem
    have hc : ⁅y, x⁆ ∈ L := (h1.trans inf_le_right).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
      (Subgroup.commutator_mem_commutator hy hx)
    have e : y * x * y⁻¹ = ⁅y, x⁆ * x := by rw [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem hc hx

theorem reducedAggregate_le_pCoreOf' (X : Subgroup G) : reducedAggregate X ≤ pCoreOf 2 X := by
  obtain ⟨-, -, hZ⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥X) 2
  refine Subgroup.map_mono fun x' hx' => ?_
  exact (BlueprintB2.mem_centerTorsion_iff.mp (hZ hx')).1

theorem le_normalizer_reducedAggregate' (X : Subgroup G) :
    X ≤ Subgroup.normalizer (reducedAggregate X : Set G) := by
  obtain ⟨hN, -, -⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥X) 2
  have hsub : (reducedAggregate X).subgroupOf X = primeReducedAggregate (↥X) 2 :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have : ((reducedAggregate X).subgroupOf X).Normal := by
    rw [hsub]
    exact hN
  exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)

end Lem3228

open Lem3228 in
theorem stmt3_2_2_eight_proved
    : Stmt3_2_2_eight := by
  intro G _ _ T L V₀ h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV₀A, hV₀ne, hL₀V₀, hcommV₀, hlt, hirr, hhom⟩ := h.irrPlus
  set L₀ := conjClosure L T with hL₀def
  set A := reducedAggregate (L ⊔ T) with hAdef
  set V := conjClosure V₀ T with hVdef
  set C := A ⊓ Subgroup.centralizer (L₀ : Set G) with hCdef
  have hLT : L₀ ⊔ T = L ⊔ T := conjClosure_sup_eq L T
  have hLc : L ∈ cComp (L ⊔ T) := cComp_of_isLocal h.maximal.1
  have hO2ne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := h.maximal.1.2.2.2
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  obtain ⟨hA2, hAc, hOA⟩ := reducedAggregate_props (L ⊔ T)
  have hAN : L ⊔ T ≤ Subgroup.normalizer (A : Set G) := le_normalizer_reducedAggregate' _
  have hAO : A ≤ pCoreOf 2 (L ⊔ T) := reducedAggregate_le_pCoreOf' _
  have hA2g : IsPGroup 2 ↥A := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le hAO
  have hLL₀ : L ≤ L₀ := le_conjClosure L T
  have hTL₀ : T ≤ Subgroup.normalizer (L₀ : Set G) := le_normalizer_conjClosure_right L T
  have hL₀H : L₀ ≤ L ⊔ T := by rw [← hLT]; exact le_sup_left
  have hHL₀ : L ⊔ T ≤ Subgroup.normalizer (L₀ : Set G) :=
    sup_le (hLL₀.trans Subgroup.le_normalizer) hTL₀
  have hVA : V ≤ A := conjClosure_le fun t ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (hAN (Subgroup.mem_sup_right ht)) v).mp (hV₀A hv)
  have hV₀V : V₀ ≤ V := le_conjClosure V₀ T
  have hVH : V ≤ L ⊔ T := hVA.trans (hAO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure V₀ T
  have hL₀V : L₀ ≤ Subgroup.normalizer (V : Set G) := by
    refine le_normalizer_of_conj_le' fun l hl w hw => ?_
    have hle : V.map (MulAut.conj l).toMonoidHom ≤ V := by
      rw [hVdef, conjClosure, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨t, ht, v, hv, rfl⟩, rfl⟩
      have hl' : t⁻¹ * l * t ∈ L₀ := by
        have := (Subgroup.mem_normalizer_iff.mp (hTL₀ (T.inv_mem ht)) l).mp hl
        simpa using this
      have hv' := (Subgroup.mem_normalizer_iff.mp (hL₀V₀ hl') v).mp hv
      refine Subgroup.subset_closure ⟨t, ht, _, hv', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    exact hle ⟨w, hw, rfl⟩
  have hHV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := by
    rw [← hLT]
    exact sup_le hL₀V hTV
  have hL₀C : L₀ ≤ Subgroup.normalizer (C : Set G) := fun l hl =>
    mem_normalizer_inf (hAN (hL₀H hl))
      (B2F.normalizer_le_normalizer_centralizer L₀ (Subgroup.le_normalizer hl))
  have hHC : L ⊔ T ≤ Subgroup.normalizer (C : Set G) := fun y hy =>
    mem_normalizer_inf (hAN hy) (B2F.normalizer_le_normalizer_centralizer L₀ (hHL₀ hy))
  have hL₀N : L₀ ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_normalizer_of_cComp h.qtke h.simple h.nonabelian hO2ne hLc
  have hOL : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
    have h1 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L L₀ hLL₀
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLL₀).mpr hL₀N)
    have h2 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L₀
      (L ⊔ T) hL₀H ((Subgroup.normal_subgroupOf_iff_le_normalizer hL₀H).mpr hHL₀)
    exact (h1.trans h2).trans (hOA.trans (Subgroup.centralizer_le hVA))
  have hcA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hAc
  have hCV₀ : C ≤ Subgroup.normalizer (V₀ : Set G) := le_normalizer_of_conj_le' fun c hc v hv => by
    rw [hcA c (Subgroup.mem_inf.mp hc).1 v (hV₀A hv), mul_inv_cancel_right]
    exact hv
  have hCVn : C ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_conj_le' fun c hc v hv => by
    rw [hcA c (Subgroup.mem_inf.mp hc).1 v (hVA hv), mul_inv_cancel_right]
    exact hv
  have hL₀VC : L₀ ≤ Subgroup.normalizer ((V ⊔ C : Subgroup G) : Set G) := fun l hl =>
    mem_normalizer_sup (hL₀V hl) (hL₀C hl)
  have hL₀K : L₀ ≤ Subgroup.normalizer ((V₀ ⊔ C : Subgroup G) : Set G) := fun l hl =>
    mem_normalizer_sup (hL₀V₀ hl) (hL₀C hl)
  have core : ∀ D' : Subgroup G, D' ≤ L ⊔ T → L ⊔ T ≤ Subgroup.normalizer (D' : Set G) →
      (∀ d ∈ D', ∃ k : ℕ, d ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G)) →
      ⁅D', L₀⁆ ≤ Subgroup.centralizer (V : Set G) → D' ≤ Subgroup.centralizer (V : Set G) := by
    intro D' hD'H hHD' h2 hcomm
    have hcen : ∀ x ∈ D', ∀ l ∈ L₀, ∀ y ∈ V ⊔ C, ⁅x, l⁆ * y = y * ⁅x, l⁆ := by
      intro x hx l hl y hy
      have hcV : ⁅x, l⁆ ∈ Subgroup.centralizer (V : Set G) :=
        hcomm (Subgroup.commutator_mem_commutator hx hl)
      have hcL : ⁅x, l⁆ ∈ L₀ := by
        rw [commutatorElement_def]
        exact L₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHL₀ (hD'H hx)) l).mp hl)
          (L₀.inv_mem hl)
      obtain ⟨v, hv, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCVn).mp hy
      have h1 : v * ⁅x, l⁆ = ⁅x, l⁆ * v := Subgroup.mem_centralizer_iff.mp hcV v hv
      have h2' : ⁅x, l⁆ * c = c * ⁅x, l⁆ :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _ hcL
      calc ⁅x, l⁆ * (v * c) = v * (⁅x, l⁆ * c) := by rw [← mul_assoc, ← h1, mul_assoc]
        _ = v * c * ⁅x, l⁆ := by rw [h2', mul_assoc]
    have hB : ∀ x ∈ D', ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀ ⊔ C := by
      intro x hx
      have hxH := hD'H hx
      have hKA : V₀ ⊔ C ≤ A := sup_le hV₀A inf_le_left
      have hJA : (V₀ ⊔ C).map (MulAut.conj x).toMonoidHom ≤ A := by
        rintro _ ⟨k, hk, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hAN hxH) k).mp (hKA hk)
      have hCJ : C ≤ (V₀ ⊔ C).map (MulAut.conj x).toMonoidHom := by
        intro c hc
        refine ⟨x⁻¹ * c * x, Subgroup.mem_sup_right ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hHC (inv_mem hxH)) c).mp hc
          simpa using this
        · simp [MulAut.conj_apply, mul_assoc]
      have hJV : (V₀ ⊔ C).map (MulAut.conj x).toMonoidHom ≤ V ⊔ C := by
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨v, hv, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCV₀).mp hk
        have e : (MulAut.conj x).toMonoidHom (v * c) = (x * v * x⁻¹) * (x * c * x⁻¹) := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (hHV hxH) v).mp (hV₀V hv))
          ((Subgroup.mem_normalizer_iff.mp (hHC hxH) c).mp hc)
      have hL₀J : L₀ ≤ Subgroup.normalizer
          (((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
        refine le_normalizer_of_conj_le' fun l hl j hj => ?_
        obtain ⟨k, hk, rfl⟩ := hj
        have hl' : x⁻¹ * l * x ∈ L₀ := by
          have := (Subgroup.mem_normalizer_iff.mp (hHL₀ (inv_mem hxH)) l).mp hl
          simpa using this
        have hk' := (Subgroup.mem_normalizer_iff.mp (hL₀K hl') k).mp hk
        refine ⟨_, hk', ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have hiso : IsXSectionIso L₀ C ((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom) (V₀ ⊔ C) := by
        have hnK : (C.subgroupOf (V₀ ⊔ C)).Normal :=
          normal_subgroupOf_of_commute fun a ha b hb => hcA a (hKA ha) b (hKA hb)
        have hnJ : (C.subgroupOf ((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom)).Normal :=
          normal_subgroupOf_of_commute fun a ha b hb => hcA a (hJA ha) b (hJA hb)
        let ψ : ↥(V₀ ⊔ C) ≃* ↥((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom) :=
          (MulAut.conj x).subgroupMap (V₀ ⊔ C)
        have hψ : ∀ k : ↥(V₀ ⊔ C), ((ψ k : ↥((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom)) : G) =
            x * k * x⁻¹ := fun k => rfl
        have hCψ : (C.subgroupOf (V₀ ⊔ C)).map ψ.toMonoidHom =
            C.subgroupOf ((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom) := by
          ext j
          simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
          constructor
          · rintro ⟨k, hk, rfl⟩
            rw [hψ]
            exact (Subgroup.mem_normalizer_iff.mp (hHC hxH) k).mp hk
          · intro hj
            refine ⟨ψ.symm j, ?_, ψ.apply_symm_apply j⟩
            have h1 : x * ((ψ.symm j : ↥(V₀ ⊔ C)) : G) * x⁻¹ = j := by
              rw [← hψ, ψ.apply_symm_apply]
            have h2 : ((ψ.symm j : ↥(V₀ ⊔ C)) : G) = x⁻¹ * j * x := by rw [← h1]; group
            rw [h2]
            have := (Subgroup.mem_normalizer_iff.mp (hHC (inv_mem hxH)) (j : G)).mp hj
            simpa using this
        refine ⟨hnJ, hnK, (QuotientGroup.congr _ _ ψ hCψ).symm, ?_⟩
        intro l hl j k hj hk hjk
        rw [MulEquiv.symm_apply_eq] at hjk ⊢
        have hjk' : (j : ↥((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom) ⧸
            C.subgroupOf ((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom)) =
            ((ψ k : ↥((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom)) : ↥((V₀ ⊔ C).map
              (MulAut.conj x).toMonoidHom) ⧸
              C.subgroupOf ((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom)) := hjk
        show ((⟨l * j * l⁻¹, hj⟩ : ↥((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom)) :
            ↥((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom) ⧸
              C.subgroupOf ((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom)) =
          ((ψ ⟨l * k * l⁻¹, hk⟩ : ↥((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom)) :
            ↥((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom) ⧸
              C.subgroupOf ((V₀ ⊔ C).map (MulAut.conj x).toMonoidHom))
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hjk' ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ] at hjk' ⊢
        have hy : l * (x * k * x⁻¹) * l⁻¹ ∈ V ⊔ C :=
          (Subgroup.mem_normalizer_iff.mp (hL₀VC hl) _).mp (hJV ⟨k, k.2, rfl⟩)
        have hc := hcen x hx l hl _ hy
        have e : x * (l * k * l⁻¹) * x⁻¹ = ⁅x, l⁆ * (l * (x * k * x⁻¹) * l⁻¹) * ⁅x, l⁆⁻¹ := by
          rw [commutatorElement_def]; group
        rw [e, hc, mul_inv_cancel_right]
        have e2 : (l * j * l⁻¹)⁻¹ * (l * (x * k * x⁻¹) * l⁻¹) =
            l * ((j : G)⁻¹ * (x * k * x⁻¹)) * l⁻¹ := by group
        rw [e2]
        exact (Subgroup.mem_normalizer_iff.mp (hL₀C hl) _).mp hjk'
      have hJle := hhom _ hCJ hJV hL₀J hiso
      intro v hv
      exact hJle ⟨v, Subgroup.mem_sup_left hv, rfl⟩
    have hCs : ∀ x ∈ D', ∀ v ∈ V₀, x * v * x⁻¹ * v⁻¹ ∈ C := by
      intro x hx
      have hxH := hD'H hx
      have hxA : ∀ v ∈ A, x * v * x⁻¹ ∈ A := fun v hv =>
        (Subgroup.mem_normalizer_iff.mp (hAN hxH) v).mp hv
      let W : Subgroup G :=
        { carrier := {v | v ∈ V₀ ∧ x * v * x⁻¹ * v⁻¹ ∈ C}
          mul_mem' := by
            rintro v w ⟨hv, hvC⟩ ⟨hw, hwC⟩
            refine ⟨V₀.mul_mem hv hw, ?_⟩
            have hbw : x * w * x⁻¹ * w⁻¹ ∈ A :=
              A.mul_mem (hxA w (hV₀A hw)) (A.inv_mem (hV₀A hw))
            have h' : (x * w * x⁻¹ * w⁻¹) * v⁻¹ = v⁻¹ * (x * w * x⁻¹ * w⁻¹) :=
              hcA _ hbw _ (A.inv_mem (hV₀A hv))
            have e : x * (v * w) * x⁻¹ * (v * w)⁻¹ =
                x * v * x⁻¹ * ((x * w * x⁻¹ * w⁻¹) * v⁻¹) := by group
            rw [e, h']
            have e2 : x * v * x⁻¹ * (v⁻¹ * (x * w * x⁻¹ * w⁻¹)) =
                (x * v * x⁻¹ * v⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group
            rw [e2]
            exact C.mul_mem hvC hwC
          one_mem' := ⟨V₀.one_mem, by simp⟩
          inv_mem' := by
            rintro v ⟨hv, hvC⟩
            refine ⟨V₀.inv_mem hv, ?_⟩
            have hav : (x * v * x⁻¹)⁻¹ * v = v * (x * v * x⁻¹)⁻¹ :=
              hcA _ (A.inv_mem (hxA v (hV₀A hv))) _ (hV₀A hv)
            have e : x * v⁻¹ * x⁻¹ * v⁻¹⁻¹ = (x * v * x⁻¹)⁻¹ * v := by group
            rw [e, hav]
            have e2 : v * (x * v * x⁻¹)⁻¹ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by group
            rw [e2]
            exact C.inv_mem hvC }
      have hWV₀ : W ≤ V₀ := fun v hv => hv.1
      have hCW : V₀ ⊓ Subgroup.centralizer (L₀ : Set G) ≤ W := by
        intro v hv
        have hvC : v ∈ C :=
          Subgroup.mem_inf.mpr ⟨hV₀A (Subgroup.mem_inf.mp hv).1, (Subgroup.mem_inf.mp hv).2⟩
        exact ⟨(Subgroup.mem_inf.mp hv).1,
          C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHC hxH) v).mp hvC) (C.inv_mem hvC)⟩
      have hL₀W : L₀ ≤ Subgroup.normalizer (W : Set G) := by
        refine le_normalizer_of_conj_le' fun l hl v hv =>
          ⟨(Subgroup.mem_normalizer_iff.mp (hL₀V₀ hl) v).mp hv.1, ?_⟩
        have hy : l * (x * v * x⁻¹) * l⁻¹ ∈ V ⊔ C := by
          have h1 : x * v * x⁻¹ ∈ V ⊔ C := (sup_le_sup_right hV₀V C) (hB x hx v hv.1)
          exact (Subgroup.mem_normalizer_iff.mp (hL₀VC hl) _).mp h1
        have hc := hcen x hx l hl _ hy
        have e : x * (l * v * l⁻¹) * x⁻¹ * (l * v * l⁻¹)⁻¹ =
            ⁅x, l⁆ * (l * (x * v * x⁻¹) * l⁻¹) * ⁅x, l⁆⁻¹ * (l * v⁻¹ * l⁻¹) := by
          rw [commutatorElement_def]; group
        rw [e, hc, mul_inv_cancel_right]
        have e2 : l * (x * v * x⁻¹) * l⁻¹ * (l * v⁻¹ * l⁻¹) = l * (x * v * x⁻¹ * v⁻¹) * l⁻¹ := by
          group
        rw [e2]
        exact (Subgroup.mem_normalizer_iff.mp (hL₀C hl) _).mp hv.2
      rcases hirr W hCW hWV₀ hL₀W with hW | hW
      ·
        exfalso
        have hEA : V₀ ⊔ C ≤ A := sup_le hV₀A inf_le_left
        have hCnE : (C.subgroupOf (V₀ ⊔ C)).Normal :=
          normal_subgroupOf_of_commute fun a ha b hb => hcA a (hEA ha) b (hEA hb)
        have hE2 : IsPGroup 2 ↥(V₀ ⊔ C) := hA2g.to_le hEA
        have hEC : ¬ V₀ ⊔ C ≤ C := by
          intro hle
          apply ne_of_lt hlt
          refine le_antisymm inf_le_left (le_inf le_rfl fun v hv => ?_)
          exact (Subgroup.mem_inf.mp (hle (Subgroup.mem_sup_left hv))).2
        have hxE : x ∈ Subgroup.normalizer ((V₀ ⊔ C : Subgroup G) : Set G) := by
          have hD'E : D' ≤ Subgroup.normalizer ((V₀ ⊔ C : Subgroup G) : Set G) :=
            le_normalizer_of_conj_le' fun y hy e he => by
              obtain ⟨v, hv, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCV₀).mp he
              have e1 : y * (v * c) * y⁻¹ = (y * v * y⁻¹) * (y * c * y⁻¹) := by group
              rw [e1]
              exact Subgroup.mul_mem _ (hB y hy v hv) (Subgroup.mem_sup_right
                ((Subgroup.mem_normalizer_iff.mp (hHC (hD'H hy)) c).mp hc))
          exact hD'E hx
        obtain ⟨k, hk⟩ := h2 x hx
        have hxk : ∀ e ∈ V₀ ⊔ C, x ^ 2 ^ k * e * (x ^ 2 ^ k)⁻¹ * e⁻¹ ∈ C := by
          intro e he
          obtain ⟨v, hv, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCV₀).mp he
          have hxv : x ^ 2 ^ k * v * (x ^ 2 ^ k)⁻¹ = v := by
            have := Subgroup.mem_centralizer_iff.mp hk v (hV₀V hv)
            rw [← this, mul_inv_cancel_right]
          have hxc : x ^ 2 ^ k * c * (x ^ 2 ^ k)⁻¹ ∈ C :=
            (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hHC hxH) _) c).mp hc
          have hc' := C.mul_mem hxc (C.inv_mem hc)
          have hcomm' : v * (x ^ 2 ^ k * c * (x ^ 2 ^ k)⁻¹ * c⁻¹) =
              (x ^ 2 ^ k * c * (x ^ 2 ^ k)⁻¹ * c⁻¹) * v :=
            hcA _ (hV₀A hv) _ (Subgroup.mem_inf.mp hc').1
          have e1 : x ^ 2 ^ k * (v * c) * (x ^ 2 ^ k)⁻¹ * (v * c)⁻¹ =
              (x ^ 2 ^ k * v * (x ^ 2 ^ k)⁻¹) * (x ^ 2 ^ k * c * (x ^ 2 ^ k)⁻¹ * c⁻¹) * v⁻¹ := by
            group
          rw [e1, hxv, hcomm', mul_inv_cancel_right]
          exact hc'
        obtain ⟨e, he, heC, hxe⟩ := exists_fixed_mod hCnE hE2 hEC hxE (hHC hxH) hxk
        obtain ⟨v, hv, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCV₀).mp he
        have hvC : v ∉ C := fun hvC => heC (C.mul_mem hvC hc)
        have hvW : v ∈ W := by
          refine ⟨hv, ?_⟩
          have hbc : x * c * x⁻¹ * c⁻¹ ∈ C :=
            C.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHC hxH) c).mp hc) (C.inv_mem hc)
          have h' : (x * c * x⁻¹ * c⁻¹) * v⁻¹ = v⁻¹ * (x * c * x⁻¹ * c⁻¹) :=
            hcA _ (Subgroup.mem_inf.mp hbc).1 _ (A.inv_mem (hV₀A hv))
          have e3 : x * v * x⁻¹ * v⁻¹ =
              (x * (v * c) * x⁻¹ * (v * c)⁻¹) * (x * c * x⁻¹ * c⁻¹)⁻¹ := by
            calc x * v * x⁻¹ * v⁻¹ = x * v * x⁻¹ * (v⁻¹ * (x * c * x⁻¹ * c⁻¹)) *
                  (x * c * x⁻¹ * c⁻¹)⁻¹ := by group
              _ = x * v * x⁻¹ * ((x * c * x⁻¹ * c⁻¹) * v⁻¹) * (x * c * x⁻¹ * c⁻¹)⁻¹ := by
                  rw [h']
              _ = _ := by group
          rw [e3]
          exact C.mul_mem hxe (C.inv_mem hbc)
        have hvW' : v ∈ V₀ ⊓ Subgroup.centralizer (L₀ : Set G) := by rw [← hW]; exact hvW
        exact hvC (Subgroup.mem_inf.mpr ⟨hV₀A hv, (Subgroup.mem_inf.mp hvW').2⟩)
      · intro v hv
        have : v ∈ W := by rw [hW]; exact hv
        exact this.2
    have hD1 : ⁅⁅L₀, D'⁆, V₀⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm.trans (Subgroup.centralizer_le hV₀V)
    have hD2 : ⁅⁅D', V₀⁆, L₀⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
      intro x hx v hv
      have := (Subgroup.mem_inf.mp (hCs x hx v hv)).2
      rwa [commutatorElement_def]
    have hD3 : ⁅⁅V₀, L₀⁆, D'⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hD1 hD2
    rw [hcommV₀, Subgroup.commutator_eq_bot_iff_le_centralizer] at hD3
    have hDV₀ : D' ≤ Subgroup.centralizer (V₀ : Set G) := Subgroup.le_centralizer_iff.mp hD3
    have hVD : V ≤ Subgroup.centralizer (D' : Set G) := by
      refine conjClosure_le fun t ht v hv => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : t⁻¹ * y * t ∈ D' := by
        have := (Subgroup.mem_normalizer_iff.mp
          (hHD' (Subgroup.mem_sup_right (T.inv_mem ht))) y).mp hy
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp (hDV₀ hy') v hv
      calc y * (t * v * t⁻¹) = t * ((t⁻¹ * y * t) * v) * t⁻¹ := by group
        _ = t * (v * (t⁻¹ * y * t)) * t⁻¹ := by rw [← hc]
        _ = t * v * t⁻¹ * y := by group
    exact Subgroup.le_centralizer_iff.mp hVD
  have hred : IsTwoReducedIn (L ⊔ T) V := by
    refine ⟨hVH, hHV, ⟨⟨⟨fun a b => Subtype.ext (hcA a (hVA a.2) b (hVA b.2))⟩⟩,
      fun v hv => hA2 v (hVA hv)⟩, ?_⟩
    intro D hDH hHD h2
    have hHN : L ⊔ T ≤ Subgroup.normalizer ((D ⊓ L₀ : Subgroup G) : Set G) := fun y hy =>
      mem_normalizer_inf (hHD hy) (hHL₀ hy)
    have hNL : D ⊓ L₀ ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans hL₀N
    have hLN : L ≤ Subgroup.normalizer ((D ⊓ L₀ : Subgroup G) : Set G) := fun y hy =>
      hHN (Subgroup.mem_sup_left hy)
    have hK1 : ⁅D ⊓ L₀, L⁆ ≤ L := commutator_le_right_of_le_normalizer hNL
    have hLK1 : L ≤ Subgroup.normalizer ((⁅D ⊓ L₀, L⁆ : Subgroup G) : Set G) := fun y hy =>
      mem_normalizer_commutator (hLN hy) (Subgroup.le_normalizer hy)
    have hK1N : ⁅D ⊓ L₀, L⁆ ≤ D ⊓ L₀ := commutator_le_left_of_le_normalizer hLN
    have hK1C := le_centralizer_of_two h.quasisimple hperf (le_sup_left.trans hHV) hOL hK1 hLK1
      (fun k hk => h2 k (Subgroup.mem_inf.mp (hK1N hk)).1)
    have hL₀N' : ⁅L₀, D ⊓ L₀⁆ ≤ Subgroup.centralizer (V : Set G) :=
      commutator_conjClosure_le le_sup_right le_sup_left hHN
        (fun y hy => B2F.normalizer_le_normalizer_centralizer V (hHV hy))
        (by rw [Subgroup.commutator_comm]; exact hK1C)
    have hNC := core (D ⊓ L₀) (inf_le_left.trans hDH) hHN
      (fun d hd => h2 d (Subgroup.mem_inf.mp hd).1)
      (by rw [Subgroup.commutator_comm]; exact hL₀N')
    have hDL₀ : ⁅D, L₀⁆ ≤ D ⊓ L₀ := le_inf (commutator_le_left_of_le_normalizer
      (hL₀H.trans hHD)) (commutator_le_right_of_le_normalizer (hDH.trans hHL₀))
    exact core D hDH hHD h2 (hDL₀.trans hNC)
  have hLV : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hLC
    have hL₀C' : L₀ ≤ Subgroup.centralizer (V : Set G) := conjClosure_le fun t ht l hl => by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : t⁻¹ * v * t ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem ht)) v).mp hv
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp (hLC hl) _ hv'
      calc v * (t * l * t⁻¹) = t * ((t⁻¹ * v * t) * l) * t⁻¹ := by group
        _ = t * (l * (t⁻¹ * v * t)) * t⁻¹ := by rw [hc]
        _ = t * l * t⁻¹ * v := by group
    apply hV₀ne
    rw [← hcommV₀, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp (hL₀C'.trans (Subgroup.centralizer_le hV₀V))
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, h.sylow.1,
    fun hd => h.sylow.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hq' : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.Open.pCore 2 ↥L) :=
    B1Red.isQuasisimple_to_open (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (BlueprintB2.pCore_eq_open_pCore 2 ↥L)) h.quasisimple)
  obtain ⟨-, hTC, -⟩ := centralizer_reduced_of_cComp hLc hq' hTsyl hred hLV
  refine ⟨by rw [hLT]; exact hVH, ?_, ?_⟩
  · rw [hLT]
    exact (isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hred).2
  · rw [hLT]
    exact hTC.symm

end CFSG.Quasithin.H13
