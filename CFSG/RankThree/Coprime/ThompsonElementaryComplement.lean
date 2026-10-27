module

public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.GroupTheory.SteinbergBKPNilpotentQuotientCore
public import CFSG.GroupTheory.SteinbergBSPrimeQuotientObstruction
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.Quasithin.Background.BlueprintB2Thompson
public import CFSG.RankThree.Coprime.ThetaPlaneNormalizesComponent
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG CFSG.GroupTheory

section Permanence

variable {p : ℕ}

theorem hasNormalPComplement_of_surjective_hom {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Surjective f) (h : HasNormalPComplement p X) :
    HasNormalPComplement p Y := by
  obtain ⟨N, hN, hNc, hNp⟩ := h
  have hNf : (N.map f).Normal := hN.map f hf
  refine ⟨N.map f, hNf, Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (H := N) f) hNc, ?_⟩
  have hle : N ≤ (N.map f).comap f := Subgroup.le_comap_map f N
  let φ : X ⧸ N →* Y ⧸ N.map f := QuotientGroup.map N (N.map f) f hle
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact hNp.of_surjective φ hφ

theorem hasNormalPComplement_map {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G')
    {K : Subgroup G} (h : HasNormalPComplement p K) : HasNormalPComplement p (K.map f) :=
  hasNormalPComplement_of_surjective_hom (f.subgroupMap K) (f.subgroupMap_surjective K) h

theorem hasNormalPComplement_subgroupOf {G : Type*} [Group G] {K : Subgroup G}
    (L : Subgroup G) (h : HasNormalPComplement p K) :
    HasNormalPComplement p (K.subgroupOf L) := by
  apply hasNormalPComplement_of_map_subtype p L
  rw [subgroupOf_map_subtype]
  exact hasNormalPComplement_of_le p inf_le_left h

end Permanence

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem map_map_center_subtype {f : G →* G'} {X : Subgroup G}
    (hf : Function.Injective (f.comp X.subtype)) :
    ((center X).map X.subtype).map f = (center (X.map f)).map (X.map f).subtype := by
  ext y
  rw [mem_map_center_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzX, hzc⟩ := mem_map_center_iff.mp hz
    refine ⟨mem_map_of_mem f hzX, ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, hzc l hl]
  · rintro ⟨⟨x, hxX, rfl⟩, hcomm⟩
    refine ⟨x, mem_map_center_iff.mpr ⟨hxX, fun l hl => ?_⟩, rfl⟩
    have h := hcomm (f l) (mem_map_of_mem f hl)
    rw [← map_mul, ← map_mul] at h
    have h' : (f.comp X.subtype) ⟨l * x, X.mul_mem hl hxX⟩ =
        (f.comp X.subtype) ⟨x * l, X.mul_mem hxX hl⟩ := h
    exact congrArg Subtype.val (hf h')

omit [Group G] [Group G'] in
theorem exists_elementary_card_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (p r : ℕ) (h : ∃ A : Subgroup X, IsElementaryAbelian p A ∧ Nat.card A = p ^ r) :
    ∃ A : Subgroup Y, IsElementaryAbelian p A ∧ Nat.card A = p ^ r := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A.map e.toMonoidHom, Quasithin.BlueprintB2.isElementaryAbelian_map hA e.toMonoidHom,
    by rw [Subgroup.card_map_of_injective e.injective, hc]⟩

omit [Group G] [Group G'] in
theorem pRank_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    pRank p X = pRank p Y := CFSG.pRank_congr_of_mulEquiv e p

omit [Group G] [Group G'] in
theorem mem_elemThompsonFamily_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (p : ℕ) {A : Subgroup X} (hA : A ∈ elemThompsonFamily X p) :
    A.map e.toMonoidHom ∈ elemThompsonFamily Y p :=
  ⟨Quasithin.BlueprintB2.isElementaryAbelian_map hA.1 e.toMonoidHom, by
    rw [Subgroup.card_map_of_injective e.injective, hA.2, pRank_eq_of_mulEquiv e p]⟩

omit [Group G] [Group G'] in
theorem elemThompson_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    (elemThompson X p).map e.toMonoidHom = elemThompson Y p := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (mem_elemThompsonFamily_map_mulEquiv e p hA)
  · refine sSup_le fun B hB => ?_
    have hB' : B.map e.symm.toMonoidHom ∈ elemThompsonFamily X p :=
      mem_elemThompsonFamily_map_mulEquiv e.symm p hB
    intro y hy
    have : e.symm y ∈ elemThompson X p := le_sSup hB' ⟨y, hy, rfl⟩
    exact ⟨e.symm y, this, e.apply_symm_apply y⟩

theorem map_map_elemThompson_subtype {f : G →* G'} {X : Subgroup G}
    (hf : Function.Injective (f.comp X.subtype)) (p : ℕ) :
    ((elemThompson X p).map X.subtype).map f =
      (elemThompson (X.map f) p).map (X.map f).subtype := by
  have hrange : (f.comp X.subtype).range = X.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : X ≃* X.map f := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)
  have hcomp : (X.map f).subtype.comp e.toMonoidHom = f.comp X.subtype := by
    ext x
    rfl
  rw [← elemThompson_map_mulEquiv e p, Subgroup.map_map, Subgroup.map_map, hcomp]

omit [Group G'] in
theorem map_subtype_centralizer (L : Subgroup G) (K : Subgroup L) :
    (centralizer (K : Set L)).map L.subtype =
      L ⊓ centralizer ((K.map L.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hy k hk)
  · intro hx
    obtain ⟨hxL, hx⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxL⟩, mem_centralizer_iff.mpr fun k hk => ?_, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.mp hx _ ⟨k, hk, rfl⟩)

omit [Group G'] in
theorem map_subtype_normalizer (L : Subgroup G) (K : Subgroup L) :
    (normalizer (K : Set L)).map L.subtype =
      L ⊓ normalizer ((K.map L.subtype : Subgroup G) : Set G) := by
  have hK : (K.map L.subtype).subgroupOf L = K :=
    comap_map_eq_self_of_injective L.subtype_injective K
  have h := subgroupOf_normalizer_eq (map_subtype_le K)
  rw [hK] at h
  rw [← h, subgroupOf_map_subtype, inf_comm]

omit [Group G'] in
theorem hyp_subgroup (p : ℕ) (L : Subgroup G) (S' : Subgroup L)
    (hC : HasNormalPComplement p ↥(L ⊓ centralizer
      (((center (S'.map L.subtype)).map (S'.map L.subtype).subtype : Subgroup G) : Set G)))
    (hN : HasNormalPComplement p ↥(L ⊓ normalizer
      (((elemThompson (S'.map L.subtype) p).map (S'.map L.subtype).subtype : Subgroup G) :
        Set G))) :
    HasNormalPComplement p ↥(centralizer (((center S').map S'.subtype : Subgroup L) : Set L)) ∧
      HasNormalPComplement p
        ↥(normalizer (((elemThompson S' p).map S'.subtype : Subgroup L) : Set L)) := by
  have hinj : Function.Injective (L.subtype.comp S'.subtype) :=
    L.subtype_injective.comp S'.subtype_injective
  constructor
  · apply hasNormalPComplement_of_map_subtype p L
    rw [map_subtype_centralizer, map_map_center_subtype hinj]
    exact hC
  · apply hasNormalPComplement_of_map_subtype p L
    rw [map_subtype_normalizer, map_map_elemThompson_subtype hinj]
    exact hN

end Transport


section Helpers

variable {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G]

theorem elemThompson_ne_bot {S : Type*} [Group S] [Finite S] [Nontrivial S] (hS : IsPGroup p S) :
    elemThompson S p ≠ ⊥ := by
  intro hJ
  obtain ⟨A, hA, hAc⟩ := Quasithin.BlueprintB2.exists_card_eq_pow_pRank S p
  have hAJ : A ≤ elemThompson S p := le_sSup ⟨hA, hAc⟩
  rw [hJ, le_bot_iff] at hAJ
  rw [hAJ, Subgroup.card_bot] at hAc
  have hdvd : p ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
    have h1 : 1 < Nat.card S := Finite.one_lt_card
    rw [hn] at h1 ⊢
    exact dvd_pow_self p (by rintro rfl; simp at h1)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hE : IsElementaryAbelian p (zpowers x) :=
    Quasithin.BlueprintB2.isElementaryAbelian_iff.mpr
      ⟨fun a ha b hb => by
          obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
          rw [← zpow_add, ← zpow_add, add_comm],
        fun a ha => by
          obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx,
            pow_orderOf_eq_one, one_zpow]⟩
  have hle := Quasithin.BlueprintB2.card_le_pow_pRank (R := S) hE
  rw [Nat.card_zpowers, hx, ← hAc] at hle
  exact absurd hle (not_le.mpr hp.out.one_lt)

theorem map_elemThompson_ne_bot [Finite G] {S : Subgroup G} (hS : IsPGroup p S) (hS1 : S ≠ ⊥) :
    (elemThompson S p).map S.subtype ≠ ⊥ := by
  have : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hS1
  rw [Ne, map_eq_bot_iff_of_injective _ S.subtype_injective]
  exact elemThompson_ne_bot hS

theorem map_center_ne_bot [Finite G] {S : Subgroup G} (hS : IsPGroup p S) (hS1 : S ≠ ⊥) :
    (center S).map S.subtype ≠ ⊥ := by
  have : Nontrivial S := (nontrivial_iff_ne_bot S).mpr hS1
  have := hS.center_nontrivial
  rw [Ne, map_eq_bot_iff_of_injective _ S.subtype_injective]
  exact (nontrivial_iff_ne_bot _).mp this

omit hp in
theorem normalizer_le_normalizer_map_elemThompson [Finite G] [Fact p.Prime] (S : Subgroup G) :
    normalizer (S : Set G) ≤
      normalizer (((elemThompson S p).map S.subtype : Subgroup G) : Set G) := by
  have : (elemThompson S p).Characteristic :=
    Quasithin.BlueprintB2.elemThompson_characteristic S p
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic _ _

omit hp in
theorem normalizer_le_normalizer_map_center (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (((center S).map S.subtype : Subgroup G) : Set G) :=
  BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic _ _

omit hp in
theorem centralizer_center_le {P S : Subgroup G} (hSP : S ≤ P)
    (hZS : (center P).map P.subtype ≤ S) :
    centralizer (((center S).map S.subtype : Subgroup G) : Set G) ≤
      centralizer (((center P).map P.subtype : Subgroup G) : Set G) := by
  apply centralizer_le
  intro z hz
  obtain ⟨hzP, hzc⟩ := mem_map_center_iff.mp hz
  exact mem_map_center_iff.mpr ⟨hZS hz, fun l hl => hzc l (hSP hl)⟩

omit hp in
theorem hasNormalPComplement_normalizer_map_conj (g : G) (T : Subgroup G) :
    HasNormalPComplement p ↥(normalizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) :
      Set G)) ↔ HasNormalPComplement p ↥(normalizer (T : Set G)) := by
  rw [← map_equiv_normalizer_eq T (MulAut.conj g)]
  let e := (normalizer (T : Set G)).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  exact ⟨hasNormalPComplement_of_equiv p e.symm, hasNormalPComplement_of_equiv p e⟩

omit hp in
theorem lt_inf_normalizer {P S : Subgroup G} [Group.IsNilpotent P] (hSP : S < P) :
    S < P ⊓ normalizer (S : Set G) := by
  have hlt : S.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hSP.ne
    apply le_antisymm hSP.le
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ S.subgroupOf P := h ▸ mem_top _
    exact this
  have h := Group.normalizerCondition_of_isNilpotent (S.subgroupOf P) hlt
  rw [← subgroupOf_normalizer_eq hSP.le] at h
  have h2 := (map_lt_map_iff_of_injective P.subtype_injective).mpr h
  rwa [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left hSP.le, inf_comm] at h2

end Helpers

section CoprimeDecomposition

open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G]

theorem commutator_inf_centralizer_eq_bot [Finite G] {B K : Subgroup G}
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hBK : B ≤ normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card K)) :
    ⁅B, K⁆ ⊓ centralizer (B : Set G) = ⊥ := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  have _ : IsMulCommutative K := ⟨⟨fun x y => Subtype.ext (hK x x.2 y y.2)⟩⟩
  have hconj : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K := fun b hb k hk =>
    (mem_normalizer_iff.mp (hBK hb) k).mp hk
  let f : B → K → K := fun b k => ⟨(b : G) * k * (b : G)⁻¹, hconj b b.2 k k.2⟩
  have hfmul : ∀ b k₁ k₂, f b (k₁ * k₂) = f b k₁ * f b k₂ := fun b k₁ k₂ =>
    Subtype.ext (by simp only [f, Subgroup.coe_mul]; group)
  let σ : K →* K := MonoidHom.mk' (fun k => ∏ b : B, f b k) fun k₁ k₂ => by
    show ∏ b, f b (k₁ * k₂) = (∏ b, f b k₁) * ∏ b, f b k₂
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => hfmul b k₁ k₂
  have hσ : ∀ k, σ k = ∏ b : B, f b k := fun k => rfl
  have hker : ⁅B, K⁆ ≤ σ.ker.map K.subtype := by
    rw [Subgroup.commutator_le]
    intro b hb k hk
    refine ⟨⟨b * k * b⁻¹, hconj b hb k hk⟩ * ⟨k, hk⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, hσ, hσ]
      exact Fintype.prod_equiv (Equiv.mulRight (⟨b, hb⟩ : B)) _ _ fun c =>
        Subtype.ext (by simp only [f, Equiv.coe_mulRight, Subgroup.coe_mul, mul_inv_rev]; group)
    · simp [commutatorElement_def]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxc, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk, rfl⟩ := hker hxc
  have hfix : ∀ b : B, f b k = k := fun b => Subtype.ext (by
    have hb : (b : G) * k = k * b := mem_centralizer_iff.mp hxB b b.2
    show (b : G) * k * (b : G)⁻¹ = k
    rw [hb, mul_inv_cancel_right])
  have h1 : k ^ Fintype.card B = 1 := by
    rw [← MonoidHom.mem_ker.mp hk, hσ]
    simp only [hfix, Finset.prod_const, Finset.card_univ]
  have h2 : k ^ Nat.card K = 1 := pow_card_eq_one'
  have h3 := (pow_gcd_eq_one (a := k)).mpr ⟨h1, h2⟩
  rw [← Nat.card_eq_fintype_card, Nat.Coprime.gcd_eq_one hcop, pow_one] at h3
  rw [h3, Subgroup.mem_bot]
  rfl

end CoprimeDecomposition

section QuotientStructure

open scoped Pointwise

variable {p : ℕ} [hp : Fact p.Prime] {X : Type*} [Group X] [Finite X]

omit hp [Finite X] in
theorem le_normalizer_of_forall_conj_mem {B K : Subgroup X}
    (h : ∀ x ∈ B, ∀ k ∈ K, x * k * x⁻¹ ∈ K) : B ≤ normalizer (K : Set X) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro k
  refine ⟨h x hx k, fun hk => ?_⟩
  have h1 := h x⁻¹ (B.inv_mem hx) _ hk
  rwa [show x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k by group] at h1

theorem card_mul_card_le (Pb : Sylow p X) {H : Subgroup X} (hH : ¬ p ∣ Nat.card H) :
    Nat.card H * Nat.card (Pb : Subgroup X) ≤ Nat.card X := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Pb.isPGroup'
  have hcop : Nat.Coprime (Nat.card H) (Nat.card (Pb : Subgroup X)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hH).symm
  exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_subgroup_dvd_card H)
    (Subgroup.card_subgroup_dvd_card _))

theorem eq_bot_or_eq_of_le_normalizer (Pb : Sylow p X) {H : Subgroup X} (hH : ¬ p ∣ Nat.card H)
    (hmax : ∀ K : Subgroup X, (Pb : Subgroup X) ≤ K → K = Pb ∨ K = ⊤) {K : Subgroup X}
    (hKH : K ≤ H) (hPK : (Pb : Subgroup X) ≤ normalizer (K : Set X)) : K = ⊥ ∨ K = H := by
  have hinf : (Pb : Subgroup X) ⊓ H = ⊥ :=
    SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hH Pb.isPGroup'
  rcases hmax (K ⊔ Pb) le_sup_right with h | h
  · left
    rw [eq_bot_iff, ← hinf]
    exact le_inf (le_sup_left.trans h.le) hKH
  · right
    have hcoe := coe_mul_of_right_le_normalizer_left K Pb hPK
    rw [h, Subgroup.coe_top] at hcoe
    have hcard : Nat.card X ≤ Nat.card K * Nat.card (Pb : Subgroup X) := by
      calc Nat.card X = Nat.card (Set.univ : Set X) := Nat.card_univ.symm
        _ = Nat.card ((K : Set X) * ((Pb : Subgroup X) : Set X)) := by rw [hcoe]
        _ ≤ Nat.card (K : Set X) * Nat.card ((Pb : Subgroup X) : Set X) := Set.natCard_mul_le
        _ = Nat.card K * Nat.card (Pb : Subgroup X) := rfl
    have h2 := (card_mul_card_le Pb hH).trans hcard
    have hK : Nat.card H ≤ Nat.card K := Nat.le_of_mul_le_mul_right h2 Nat.card_pos
    exact (eq_of_le_of_card_ge hKH hK)

omit [Finite X] in
theorem sup_eq_top_of_max (Pb : Sylow p X) {H : Subgroup X} (hH : ¬ p ∣ Nat.card H)
    (hmax : ∀ K : Subgroup X, (Pb : Subgroup X) ≤ K → K = Pb ∨ K = ⊤) (hH1 : H ≠ ⊥) :
    (Pb : Subgroup X) ⊔ H = ⊤ := by
  rcases hmax ((Pb : Subgroup X) ⊔ H) le_sup_left with h | h
  · exfalso
    apply hH1
    rw [eq_bot_iff, ← SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hH Pb.isPGroup']
    exact le_inf (le_sup_right.trans h.le) le_rfl
  · exact h

omit [Finite X] in
theorem inf_centralizer_eq_bot_of_max (Pb : Sylow p X) {H : Subgroup X} [hHn : H.Normal]
    (hH : ¬ p ∣ Nat.card H) (hmax : ∀ K : Subgroup X, (Pb : Subgroup X) ≤ K → K = Pb ∨ K = ⊤)
    (hH1 : H ≠ ⊥) (hOp : ∀ K : Subgroup X, K.Normal → IsPGroup p K → K = ⊥) :
    (Pb : Subgroup X) ⊓ centralizer (H : Set X) = ⊥ := by
  have hsup := sup_eq_top_of_max Pb hH hmax hH1
  refine hOp _ ⟨fun n hn g => ?_⟩ (Pb.isPGroup'.to_le inf_le_left)
  obtain ⟨hnP, hnC⟩ := Subgroup.mem_inf.mp hn
  have hg : g ∈ (((Pb : Subgroup X) ⊔ H : Subgroup X) : Set X) := by
    rw [hsup]
    exact Set.mem_univ g
  rw [mul_normal, Set.mem_mul] at hg
  obtain ⟨x, hx, h, hh, rfl⟩ := hg
  have hcomm : h * n = n * h := mem_centralizer_iff.mp hnC h hh
  have heq : x * h * n * (x * h)⁻¹ = x * n * x⁻¹ := by
    rw [mul_assoc x h n, hcomm]
    group
  rw [heq]
  exact Subgroup.mem_inf.mpr ⟨Pb.mul_mem (Pb.mul_mem hx hnP) (Pb.inv_mem hx),
    (Subgroup.normal_centralizer (H := H)).conj_mem n hnC x⟩

theorem exists_isElementaryAbelian_of_max (Pb : Sylow p X) {H : Subgroup X} [hHn : H.Normal]
    (hH : ¬ p ∣ Nat.card H) (hmax : ∀ K : Subgroup X, (Pb : Subgroup X) ≤ K → K = Pb ∨ K = ⊤)
    (hH1 : H ≠ ⊥) : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsElementaryAbelian q H := by
  classical
  have : Nontrivial H := (nontrivial_iff_ne_bot H).mpr hH1
  have h1 : 1 < Nat.card H := Finite.one_lt_card
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h1.ne'
  have hqp : q ≠ p := fun h => hH (h ▸ hqd)
  have : Fact q.Prime := ⟨hq⟩
  refine ⟨q, hq, hqp, ?_⟩
  let _ : MulDistribMulAction (Pb : Subgroup X) H := MulDistribMulAction.compHom H
    ((MulAut.conjNormal : X →* MulAut H).comp (Pb : Subgroup X).subtype)
  have hsmul : ∀ (x : (Pb : Subgroup X)) (h : H), ((x • h : H) : X) = x * h * x⁻¹ :=
    fun x h => rfl
  obtain ⟨R, hR⟩ : ∃ R : Sylow q H, ∀ x : (Pb : Subgroup X), x • R = R := by
    by_contra hnone
    simp only [not_exists, not_forall] at hnone
    have hmod := Pb.isPGroup'.card_modEq_card_fixedPoints (Sylow q H)
    have hempty : Nat.card (MulAction.fixedPoints (Pb : Subgroup X) (Sylow q H)) = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨R, hR⟩
      obtain ⟨x, hx⟩ := hnone R
      exact hx (hR x)
    rw [hempty] at hmod
    apply hH
    have hdvd : p ∣ Nat.card (Sylow q H) := Nat.modEq_zero_iff_dvd.mp hmod
    exact hdvd.trans ((default : Sylow q H).card_dvd_index.trans (Subgroup.index_dvd_card _))
  set R' : Subgroup X := (R : Subgroup H).map H.subtype with hR'
  have hR'P : (Pb : Subgroup X) ≤ normalizer (R' : Set X) := by
    apply le_normalizer_of_forall_conj_mem
    rintro x hx _ ⟨r, hr, rfl⟩
    have hxR : (⟨x, hx⟩ : (Pb : Subgroup X)) • (R : Subgroup H) = R := by
      rw [← Sylow.pointwise_smul_def, hR]
    have hmem : (⟨x, hx⟩ : (Pb : Subgroup X)) • r ∈ (R : Subgroup H) := by
      rw [← hxR]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hr
    exact ⟨_, hmem, hsmul _ r⟩
  have hR'1 : R' ≠ ⊥ := by
    rw [hR', Ne, map_eq_bot_iff_of_injective _ H.subtype_injective]
    exact R.ne_bot_of_dvd_card hqd
  have hR'H : R' = H :=
    (eq_bot_or_eq_of_le_normalizer Pb hH hmax (map_subtype_le _) hR'P).resolve_left hR'1
  have hHq : IsPGroup q H := by
    have h := R.isPGroup'.map H.subtype
    rw [← hR', hR'H] at h
    exact h
  set E := Quasithin.BlueprintB2.centerTorsion q H with hE
  have hEP : (Pb : Subgroup X) ≤ normalizer (E : Set X) := by
    apply le_normalizer_of_forall_conj_mem
    intro x _ z hz
    obtain ⟨hzH, hzc, hzq⟩ := Quasithin.BlueprintB2.mem_centerTorsion_iff.mp hz
    refine Quasithin.BlueprintB2.mem_centerTorsion_iff.mpr
      ⟨hHn.conj_mem z hzH x, fun k hk => ?_, ?_⟩
    · have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ H := hHn.conj_mem k hk x⁻¹
      rw [inv_inv] at hk'
      have h := hzc _ hk'
      calc k * (x * z * x⁻¹) = x * ((x⁻¹ * k * x) * z) * x⁻¹ := by group
        _ = x * (z * (x⁻¹ * k * x)) * x⁻¹ := by rw [h]
        _ = x * z * x⁻¹ * k := by group
    · rw [conj_pow, hzq, mul_one, mul_inv_cancel]
  have hE1 : E ≠ ⊥ := by
    have hZ := hHq.center_nontrivial
    have hZq : IsPGroup q (center H) := hHq.to_subgroup _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card (α := center H)).ne' hk
    have hqZ : q ∣ Nat.card (center H) := hk ▸ dvd_pow_self q hk0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hqZ
    intro hEbot
    have hzE : ((z : H) : X) ∈ E := by
      refine Quasithin.BlueprintB2.mem_centerTorsion_iff.mpr ⟨(z : H).2, fun k hk => ?_, ?_⟩
      · exact congrArg Subtype.val (mem_center_iff.mp z.2 ⟨k, hk⟩)
      · have h := pow_orderOf_eq_one z
        rw [hz] at h
        have h' := congrArg (fun w : center H => ((w : H) : X)) h
        simpa using h'
    rw [hEbot, Subgroup.mem_bot] at hzE
    have hz1 : z = 1 := Subtype.ext (Subtype.ext hzE)
    rw [hz1, orderOf_one] at hz
    exact hq.one_lt.ne hz
  have hEH : E = H := (eq_bot_or_eq_of_le_normalizer Pb hH hmax
    (Quasithin.BlueprintB2.centerTorsion_le q H) hEP).resolve_left hE1
  refine Quasithin.BlueprintB2.isElementaryAbelian_iff.mpr ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have hb' : b ∈ E := hEH ▸ hb
    exact (Quasithin.BlueprintB2.mem_centerTorsion_iff.mp hb').2.1 a ha
  · have ha' : a ∈ E := hEH ▸ ha
    exact (Quasithin.BlueprintB2.mem_centerTorsion_iff.mp ha').2.2

theorem card_eq_prime_of_irreducible {B H : Subgroup X} [hHn : H.Normal]
    [hB : IsElementaryAbelian p B] (hB1 : B ≠ ⊥) (hH : ¬ p ∣ Nat.card H) (hH1 : H ≠ ⊥)
    (hirr : ∀ K : Subgroup X, K ≤ H → B ≤ normalizer (K : Set X) → K = ⊥ ∨ K = H)
    (hfaith : B ⊓ centralizer (H : Set X) = ⊥) : Nat.card B = p := by
  classical
  have hBp : IsPGroup p B := IsElementaryAbelian.isPGroup p B
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hB1 (Subgroup.card_eq_one.mp hk)
  by_contra hne
  have hk2 : 2 ≤ k := by
    by_contra h
    apply hne
    rw [hk, show k = 1 by omega, pow_one]
  have hcard : p ^ 2 ≤ Nat.card B := hk ▸ Nat.pow_le_pow_right hp.out.pos hk2
  let _ : MulDistribMulAction B H := MulDistribMulAction.compHom H
    ((MulAut.conjNormal : X →* MulAut H).comp B.subtype)
  have hsmul : ∀ (b : B) (h : H), ((b • h : H) : X) = b * h * b⁻¹ := fun b h => rfl
  have hgen := SolvableHall.coprime_centralizer_generation (p := p) (A := B) (H := H) hcard hH
  have : Nontrivial H := (nontrivial_iff_ne_bot H).mpr hH1
  obtain ⟨b, hb1, hb⟩ : ∃ b : B, b ≠ 1 ∧ fixedPointSubgroup (zpowers b) H ≠ ⊥ := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply (top_ne_bot : (⊤ : Subgroup H) ≠ ⊥)
    rw [← hgen]
    exact iSup₂_eq_bot.mpr fun b hb => hall b hb
  set K := (fixedPointSubgroup (zpowers b) H).map H.subtype with hK
  have hKB : B ≤ normalizer (K : Set X) := by
    apply le_normalizer_of_forall_conj_mem
    rintro x hx _ ⟨y, hy, rfl⟩
    refine ⟨(⟨x, hx⟩ : B) • y, ?_, hsmul _ y⟩
    have hy' := (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b y).mp hy
    refine (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b _).mpr ?_
    rw [← mul_smul, hB.toIsMulCommutative.is_comm.comm b ⟨x, hx⟩, mul_smul, hy']
  rcases hirr K (map_subtype_le _) hKB with hK1 | hKeq
  · exact hb ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp hK1)
  · apply hb1
    have hbC : (b : X) ∈ B ⊓ centralizer (H : Set X) := by
      refine Subgroup.mem_inf.mpr ⟨b.2, mem_centralizer_iff.mpr fun h hh => ?_⟩
      have hhK : h ∈ K := hKeq ▸ hh
      obtain ⟨y, hy, rfl⟩ := hhK
      have hy' := congrArg Subtype.val ((SolvableHall.mem_fixedPointSubgroup_zpowers_iff b y).mp hy)
      rw [hsmul] at hy'
      calc (H.subtype y) * b = b * y * b⁻¹ * b := by rw [hy']; rfl
        _ = b * (H.subtype y) := by simp
    rw [hfaith, Subgroup.mem_bot] at hbC
    exact Subtype.ext hbC

end QuotientStructure

section Minimal

universe u

local notation "𝒵[" X "]" => Subgroup.map (Subgroup.subtype X) (Subgroup.center X)
local notation "𝒥[" p ", " X "]" => Subgroup.map (Subgroup.subtype X) (elemThompson X p)

structure ThompsonMinimal (p : ℕ) (G : Type u) [Group G] [Finite G] (P : Sylow p G) : Prop where
  hC : HasNormalPComplement p ↥(centralizer (𝒵[(P : Subgroup G)] : Set G))
  hN : HasNormalPComplement p ↥(normalizer (𝒥[p, (P : Subgroup G)] : Set G))
  not_hnc : ¬ HasNormalPComplement p G
  ih : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G → ∀ S : Sylow p H,
    HasNormalPComplement p ↥(centralizer (𝒵[(S : Subgroup H)] : Set H)) →
    HasNormalPComplement p ↥(normalizer (𝒥[p, (S : Subgroup H)] : Set H)) →
    HasNormalPComplement p H

namespace ThompsonMinimal

variable {p : ℕ} [hp : Fact p.Prime] {G : Type u} [Group G] [Finite G] {P : Sylow p G}

omit hp in
theorem hnc_of_lt (M : ThompsonMinimal p G P) (L : Subgroup G) (hL : L ≠ ⊤) (S : Sylow p L)
    (hC : HasNormalPComplement p
      ↥(L ⊓ centralizer (𝒵[(S : Subgroup L).map L.subtype] : Set G)))
    (hN : HasNormalPComplement p
      ↥(L ⊓ normalizer (𝒥[p, (S : Subgroup L).map L.subtype] : Set G))) :
    HasNormalPComplement p L := by
  have hcard : Nat.card L < Nat.card G := by
    have h := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hL)
    rwa [Subgroup.card_top] at h
  obtain ⟨hC', hN'⟩ := hyp_subgroup p L S hC hN
  exact M.ih L hcard S hC' hN'

omit hp in
theorem hnc_of_le (M : ThompsonMinimal p G P) {L : Subgroup G} (hPL : (P : Subgroup G) ≤ L)
    (hL : L ≠ ⊤) : HasNormalPComplement p L := by
  have hS : ((P.subtype hPL : Sylow p L) : Subgroup L).map L.subtype = P := by
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPL]
  apply M.hnc_of_lt L hL (P.subtype hPL)
  · rw [hS]
    exact hasNormalPComplement_of_le p inf_le_right M.hC
  · rw [hS]
    exact hasNormalPComplement_of_le p inf_le_right M.hN

theorem normalizer_ne_top (M : ThompsonMinimal p G P) :
    normalizer ((P : Subgroup G) : Set G) ≠ ⊤ := by
  intro hNP
  apply M.not_hnc
  have hJ : normalizer (𝒥[p, (P : Subgroup G)] : Set G) = ⊤ := by
    rw [eq_top_iff, ← hNP]
    exact normalizer_le_normalizer_map_elemThompson _
  have h := M.hN
  rw [hJ] at h
  exact BenderSuzuki.External.hkt_hasNormalPComplement_of_subgroup_eq_top ⊤ rfl h

theorem pPrimeCore_eq_bot (M : ThompsonMinimal p G P) : pPrimeCore p G = ⊥ := by
  by_contra hR
  set R := pPrimeCore p G with hRdef
  have hRc : Nat.Coprime p (Nat.card R) := pPrimeCore_coprime_card (p := p) (G := G)
  have hRp : ¬ p ∣ Nat.card R := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hRc
  have hcard : Nat.card (G ⧸ R) < Nat.card G := by
    have h := R.card_eq_card_quotient_mul_card_subgroup
    have h1 : 1 < Nat.card R := by
      have : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hR
      exact Finite.one_lt_card
    have h0 : 0 < Nat.card (G ⧸ R) := Nat.card_pos
    nlinarith
  set π := QuotientGroup.mk' R with hπ
  have hPp : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hinj : Function.Injective (π.comp (P : Subgroup G).subtype) :=
    (SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting hRp hPp).1
  set Pb : Sylow p (G ⧸ R) := P.mapSurjective (QuotientGroup.mk'_surjective R) with hPbdef
  have hPb : (Pb : Subgroup (G ⧸ R)) = (P : Subgroup G).map π := Sylow.coe_mapSurjective _ _
  have hZ : 𝒵[(Pb : Subgroup (G ⧸ R))] = 𝒵[(P : Subgroup G)].map π := by
    rw [hPb, map_map_center_subtype hinj]
  have hJ : 𝒥[p, (Pb : Subgroup (G ⧸ R))] = 𝒥[p, (P : Subgroup G)].map π := by
    rw [hPb, map_map_elemThompson_subtype hinj]
  have hZp : IsPGroup p 𝒵[(P : Subgroup G)] := hPp.to_le (map_subtype_le _)
  have hJp : IsPGroup p 𝒥[p, (P : Subgroup G)] := hPp.to_le (map_subtype_le _)
  have hC : HasNormalPComplement p ↥(centralizer (𝒵[(Pb : Subgroup (G ⧸ R))] : Set (G ⧸ R))) := by
    rw [hZ, (SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting hRp hZp).2.2]
    exact hasNormalPComplement_map π M.hC
  have hN : HasNormalPComplement p
      ↥(normalizer (𝒥[p, (Pb : Subgroup (G ⧸ R))] : Set (G ⧸ R))) := by
    rw [hJ, (SteinbergBS.prime_to_p_quotient_normalizer_centralizer_lifting hRp hJp).2.1]
    exact hasNormalPComplement_map π M.hN
  apply M.not_hnc
  refine hasNormalPComplement_of_surjective p π (QuotientGroup.mk'_surjective R) ?_
    (M.ih (G ⧸ R) hcard Pb hC hN)
  rw [hπ, QuotientGroup.ker_mk']
  exact hRc

theorem exists_bad (M : ThompsonMinimal p G P) : ∃ T : Subgroup G, T ≤ P ∧ T ≠ ⊥ ∧
    ¬ HasNormalPComplement p ↥(normalizer (T : Set G)) := by
  have h := M.not_hnc
  rw [hasNormalPComplement_iff_isPGroup_automizer] at h
  simp only [not_forall] at h
  obtain ⟨Q, hQ, hQnot⟩ := h
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    apply hQnot
    have hc : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [mem_centralizer_iff]
      intro y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hc]
    exact mem_top _
  have hQN : ¬ HasNormalPComplement p ↥(normalizer (Q : Set G)) := fun hc => hQnot
    (BenderSuzuki.External.hkt_normalizer_quotient_centralizer_isPGroup_of_hasNormalPComplement
      Q hQ hc)
  obtain ⟨c, -, hc⟩ := QuasiDihedralFusion.exists_conj_le_sylow ⊤ P le_top Q le_top hQ
  refine ⟨Q.map (MulAut.conj c).toMonoidHom, hc, ?_, ?_⟩
  · rwa [Ne, map_eq_bot_iff_of_injective _ (MulAut.conj c).injective]
  · rwa [hasNormalPComplement_normalizer_map_conj]

theorem pCore_ne_bot (M : ThompsonMinimal p G P) : pCore p G ≠ ⊥ := by
  classical
  set 𝒯 : Set (Subgroup G) := {T | T ≤ P ∧ T ≠ ⊥ ∧
    ¬ HasNormalPComplement p ↥(normalizer (T : Set G))} with h𝒯
  obtain ⟨T₀, hT₀⟩ := M.exists_bad
  have hne : Nonempty 𝒯 := ⟨⟨T₀, hT₀⟩⟩
  obtain ⟨⟨T, hTP, hT1, hTN⟩, hmax⟩ := Finite.exists_max
    (fun T : 𝒯 => Nat.card ↥((P : Subgroup G) ⊓ normalizer ((T : Subgroup G) : Set G)))
  simp only at hmax
  have : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
  set L := normalizer (T : Set G) with hL
  set S := (P : Subgroup G) ⊓ L with hS
  have hTS : T ≤ S := le_inf hTP le_normalizer
  have hSp : IsPGroup p S := P.isPGroup'.to_le inf_le_left
  obtain ⟨S₁, hS₁⟩ := (hSp.comap_of_injective L.subtype L.subtype_injective).exists_le_sylow
  set S₂ : Subgroup G := (S₁ : Subgroup L).map L.subtype with hS₂
  have hSS₂ : S ≤ S₂ := fun x hx => ⟨⟨x, (Subgroup.mem_inf.mp hx).2⟩, hS₁ hx, rfl⟩
  have hS₂L : S₂ ≤ L := map_subtype_le _
  have hS₂p : IsPGroup p S₂ := S₁.isPGroup'.map L.subtype
  have hTS₂ : T ≤ S₂ := by
    have hTn : (T.subgroupOf L).Normal :=
      BenderSuzuki.External.hkt_subgroupOf_normalizer_normal T
    have hTp : IsPGroup p (T.subgroupOf L) :=
      (P.isPGroup'.to_le hTP).comap_of_injective L.subtype L.subtype_injective
    have hle := hTp.le_sylow_of_normal S₁
    intro x hx
    exact ⟨⟨x, le_normalizer hx⟩, hle hx, rfl⟩
  obtain ⟨c, -, hc⟩ := QuasiDihedralFusion.exists_conj_le_sylow ⊤ P le_top S₂ le_top hS₂p
  have hT' : T.map (MulAut.conj c).toMonoidHom ∈ 𝒯 := by
    refine ⟨(map_mono hTS₂).trans hc, ?_, ?_⟩
    · rwa [Ne, map_eq_bot_iff_of_injective _ (MulAut.conj c).injective]
    · rwa [hasNormalPComplement_normalizer_map_conj]
  have hle1 : S₂.map (MulAut.conj c).toMonoidHom ≤ (P : Subgroup G) ⊓
      normalizer ((T.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
    refine le_inf hc ?_
    rw [← map_equiv_normalizer_eq T (MulAut.conj c)]
    exact map_mono hS₂L
  have hcard1 : Nat.card S₂ ≤ Nat.card S := by
    calc Nat.card S₂ = Nat.card (S₂.map (MulAut.conj c).toMonoidHom) :=
          (card_map_of_injective (MulAut.conj c).injective).symm
      _ ≤ _ := card_le_of_le hle1
      _ ≤ Nat.card S := hmax ⟨_, hT'⟩
  have hSeq : S₂ = S := (eq_of_le_of_card_ge hSS₂ hcard1).symm
  have hS1 : S ≠ ⊥ := ne_bot_of_le_ne_bot hT1 hTS
  by_cases hSP : S = P
  ·
    have hPL : (P : Subgroup G) ≤ L := by
      rw [← hSP]
      exact inf_le_right
    by_cases hLtop : L = ⊤
    · intro hbot
      apply hT1
      have hTn : T.Normal := normalizer_eq_top_iff.mp hLtop
      have hle : T ≤ pCore p G := le_sSup ⟨hTn, P.isPGroup'.to_le hTP⟩
      rw [hbot] at hle
      exact le_bot_iff.mp hle
    · exact absurd (M.hnc_of_le hPL hLtop) hTN
  · exfalso
    have hSlt : S < P := lt_of_le_of_ne inf_le_left hSP
    have hLtop : L ≠ ⊤ := by
      intro h
      apply hSP
      rw [hS, h, inf_top_eq]
    have hZS : 𝒵[(P : Subgroup G)] ≤ S := by
      intro z hz
      obtain ⟨hzP, hzc⟩ := mem_map_center_iff.mp hz
      refine Subgroup.mem_inf.mpr ⟨hzP, centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun t ht => ?_)⟩
      exact hzc t (hTP ht)
    have hS₂' : (S₁ : Subgroup L).map L.subtype = S := hSeq
    have hC' : HasNormalPComplement p
        ↥(L ⊓ centralizer (𝒵[(S₁ : Subgroup L).map L.subtype] : Set G)) := by
      rw [hS₂']
      exact hasNormalPComplement_of_le p (inf_le_right.trans (centralizer_center_le hSlt.le hZS))
        M.hC
    have hJN : ¬ HasNormalPComplement p ↥(normalizer (𝒥[p, S] : Set G)) := by
      intro h
      apply hTN
      apply M.hnc_of_lt L hLtop S₁ hC'
      rw [hS₂']
      exact hasNormalPComplement_of_le p inf_le_right h
    have hJ𝒯 : 𝒥[p, S] ∈ 𝒯 :=
      ⟨(map_subtype_le _).trans inf_le_left, map_elemThompson_ne_bot hSp hS1, hJN⟩
    have h1 := hmax ⟨_, hJ𝒯⟩
    have h2 : (P : Subgroup G) ⊓ normalizer (S : Set G) ≤
        (P : Subgroup G) ⊓ normalizer (𝒥[p, S] : Set G) :=
      inf_le_inf_left _ (normalizer_le_normalizer_map_elemThompson S)
    have h4 := card_lt_of_lt (lt_inf_normalizer hSlt)
    have h5 := card_le_of_le h2
    simp only at h1
    omega

omit hp [Finite G] in
theorem pCore_le_sylow : pCore p G ≤ (P : Subgroup G) := by
  have := pCore_normal (p := p) (G := G)
  exact (pCore_isPGroup (p := p) (G := G)).le_sylow_of_normal P

theorem hnc_quotient_pCore (M : ThompsonMinimal p G P) :
    HasNormalPComplement p (G ⧸ pCore p G) := by
  set Q := pCore p G with hQ
  have hQn : Q.Normal := pCore_normal (p := p) (G := G)
  have hQp : IsPGroup p Q := pCore_isPGroup (p := p) (G := G)
  have hQP : Q ≤ P := pCore_le_sylow
  have hQ1 : Q ≠ ⊥ := M.pCore_ne_bot
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set Pb : Sylow p (G ⧸ Q) := P.mapSurjective hπs with hPbdef
  have hPb : (Pb : Subgroup (G ⧸ Q)) = (P : Subgroup G).map π := Sylow.coe_mapSurjective _ _
  have hPbp : IsPGroup p (Pb : Subgroup (G ⧸ Q)) := Pb.isPGroup'
  have hPb1 : (Pb : Subgroup (G ⧸ Q)) ≠ ⊥ := by
    rw [hPb]
    intro h
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h
    apply M.normalizer_ne_top
    rw [le_antisymm h hQP]
    exact Subgroup.normalizer_eq_top_iff.mpr hQn
  have hcard : Nat.card (G ⧸ Q) < Nat.card G := by
    have h := Q.card_eq_card_quotient_mul_card_subgroup
    have h1 : 1 < Nat.card Q := by
      have : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hQ1
      exact Finite.one_lt_card
    have h0 : 0 < Nat.card (G ⧸ Q) := Nat.card_pos
    nlinarith
  have key : ∀ X : Subgroup (G ⧸ Q), X ≤ Pb → X ≠ ⊥ →
      (Pb : Subgroup (G ⧸ Q)) ≤ normalizer (X : Set (G ⧸ Q)) →
      HasNormalPComplement p ↥(normalizer (X : Set (G ⧸ Q))) := by
    intro X hXP hX1 hPX
    set W := X.comap π with hW
    have hWn : normalizer (W : Set G) = (normalizer (X : Set (G ⧸ Q))).comap π :=
      (comap_normalizer_eq_of_surjective X hπs).symm
    have hWP : W ≤ P := by
      have h : X.comap π ≤ (Pb : Subgroup (G ⧸ Q)).comap π := Subgroup.comap_mono hXP
      rw [hPb, comap_map_eq, hπ, QuotientGroup.ker_mk', sup_eq_left.mpr hQP] at h
      exact h
    have hPW : (P : Subgroup G) ≤ normalizer (W : Set G) := by
      rw [hWn, ← Subgroup.map_le_iff_le_comap, ← hPb]
      exact hPX
    have hWtop : normalizer (W : Set G) ≠ ⊤ := by
      intro h
      have hWnorm : W.Normal := normalizer_eq_top_iff.mp h
      have hWQ : W ≤ Q := le_sSup ⟨hWnorm, P.isPGroup'.to_le hWP⟩
      apply hX1
      rw [← map_comap_eq_self_of_surjective hπs X, eq_bot_iff, Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_bot, ← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk']
      exact hWQ hx
    have h := hasNormalPComplement_map π (M.hnc_of_le hPW hWtop)
    rwa [hWn, map_comap_eq_self_of_surjective hπs] at h
  have hZ := key _ (map_subtype_le _) (map_center_ne_bot hPbp hPb1)
    (le_normalizer.trans (normalizer_le_normalizer_map_center _))
  have hJ := key _ (map_subtype_le _) (map_elemThompson_ne_bot hPbp hPb1)
    (le_normalizer.trans (normalizer_le_normalizer_map_elemThompson _))
  exact M.ih (G ⧸ Q) hcard Pb (hasNormalPComplement_of_le p (centralizer_le_normalizer _) hZ) hJ

theorem core_centralizer (M : ThompsonMinimal p G P) :
    centralizer (pCore p G : Set G) ≤ pCore p G ∧
      ∀ H : Subgroup G, pCore p G ≤ H → HasNormalPComplement p H → IsPGroup p H := by
  have hcore := SteinbergBK.p_nilpotent_quotient_core_centralizer (p := p) M.pPrimeCore_eq_bot
    ((hasNormalPComplement_iff_exists p).mp M.hnc_quotient_pCore)
  exact ⟨hcore.1, fun H hQH hH => hcore.2 H hQH ((hasNormalPComplement_iff_exists p).mp hH)⟩

theorem eq_of_sylow_le (M : ThompsonMinimal p G P) {L : Subgroup G} (hPL : (P : Subgroup G) ≤ L) :
    L = P ∨ L = ⊤ := by
  by_cases hL : L = ⊤
  · exact Or.inr hL
  · exact Or.inl (P.is_maximal' ((M.core_centralizer).2 L (pCore_le_sylow.trans hPL)
      (M.hnc_of_le hPL hL)) hPL)

theorem false_of_minimal (hp2 : p ≠ 2) (M : ThompsonMinimal p G P) : False := by
  classical
  set Q := pCore p G with hQ
  have hQn : Q.Normal := pCore_normal (p := p) (G := G)
  have hQp : IsPGroup p Q := pCore_isPGroup (p := p) (G := G)
  have hQP : Q ≤ P := pCore_le_sylow
  obtain ⟨hCQ, hpgrp⟩ := M.core_centralizer
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hker : π.ker = Q := by rw [hπ, QuotientGroup.ker_mk']
  set Pb : Sylow p (G ⧸ Q) := P.mapSurjective hπs with hPbdef
  have hPb : (Pb : Subgroup (G ⧸ Q)) = (P : Subgroup G).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨H, hHn, hHc, hHq⟩ := M.hnc_quotient_pCore
  have hH : ¬ p ∣ Nat.card H := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hHc
  have hmax : ∀ K : Subgroup (G ⧸ Q), (Pb : Subgroup (G ⧸ Q)) ≤ K → K = Pb ∨ K = ⊤ := by
    intro K hK
    have hPK : (P : Subgroup G) ≤ K.comap π := by
      rw [← map_le_iff_le_comap, ← hPb]
      exact hK
    rcases M.eq_of_sylow_le hPK with h | h
    · left
      rw [hPb, ← h, map_comap_eq_self_of_surjective hπs]
    · right
      rw [← map_comap_eq_self_of_surjective hπs K, h, map_top_of_surjective π hπs]
  have hOp : ∀ K : Subgroup (G ⧸ Q), K.Normal → IsPGroup p K → K = ⊥ := by
    intro K hKn hKp
    have hcn : (K.comap π).Normal := hKn.comap π
    have hcp : IsPGroup p (K.comap π) := hKp.comap_of_ker_isPGroup π (by rw [hker]; exact hQp)
    have hle : K.comap π ≤ Q := le_sSup ⟨hcn, hcp⟩
    rw [← map_comap_eq_self_of_surjective hπs K, eq_bot_iff, map_le_iff_le_comap]
    intro x hx
    rw [mem_comap, mem_bot, ← MonoidHom.mem_ker, hker]
    exact hle hx
  have hH1 : H ≠ ⊥ := by
    intro hbot
    have hGQ : IsPGroup p (G ⧸ Q) := by
      intro x
      obtain ⟨k, hk⟩ := hHq (QuotientGroup.mk x)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hbot, mem_bot] at hk
      exact hk
    have hGp : IsPGroup p (⊤ : Subgroup G) := by
      have h := (hGQ.to_subgroup ⊤).comap_of_ker_isPGroup π (by rw [hker]; exact hQp)
      rwa [comap_top] at h
    apply M.normalizer_ne_top
    rw [← P.is_maximal' hGp le_top]
    exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
  obtain ⟨q, hq, hqp, hHea⟩ := exists_isElementaryAbelian_of_max Pb hH hmax hH1
  have : Fact q.Prime := ⟨hq⟩
  have hfaith := inf_centralizer_eq_bot_of_max Pb hH hmax hH1 hOp
  have hJQ : ¬ 𝒥[p, (P : Subgroup G)] ≤ Q := by
    intro hJQ
    apply M.not_hnc
    set Y := Q.subgroupOf (P : Subgroup G) with hY
    have hJY : elemThompson (P : Subgroup G) p ≤ Y := fun x hx => hJQ ⟨x, hx, rfl⟩
    have h1 := Quasithin.BlueprintB2.elemThompson_map_subtype (p := p) hJY
    have hYmap : Y.map (P : Subgroup G).subtype = Q := map_subgroupOf_eq_of_le hQP
    have h2 := map_map_elemThompson_subtype (f := (P : Subgroup G).subtype) (X := Y)
      ((P : Subgroup G).subtype_injective.comp Y.subtype_injective) p
    rw [h1, hYmap] at h2
    have hNJ : normalizer (𝒥[p, (P : Subgroup G)] : Set G) = ⊤ := by
      rw [h2, eq_top_iff, ← normalizer_eq_top_iff.mpr hQn]
      exact normalizer_le_normalizer_map_elemThompson Q
    have h := M.hN
    rw [hNJ] at h
    exact BenderSuzuki.External.hkt_hasNormalPComplement_of_subgroup_eq_top ⊤ rfl h
  obtain ⟨A, hAfam, hAQ⟩ : ∃ A ∈ elemThompsonFamily (P : Subgroup G) p,
      ¬ A.map (P : Subgroup G).subtype ≤ Q := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply hJQ
    rw [map_le_iff_le_comap]
    exact sSup_le fun A hA => map_le_iff_le_comap.mp (hall A hA)
  set A₀ := A.map (P : Subgroup G).subtype with hA₀
  have hA₀ea : IsElementaryAbelian p A₀ := Quasithin.BlueprintB2.isElementaryAbelian_map hAfam.1 _
  have hA₀P : A₀ ≤ P := map_subtype_le _
  have hAmax : ∀ B : Subgroup G, B ≤ P → IsElementaryAbelian p B → Nat.card B ≤ Nat.card A₀ := by
    intro B hBP hB
    rw [hA₀, card_map_of_injective (P : Subgroup G).subtype_injective, hAfam.2]
    have h := Quasithin.BlueprintB2.card_le_pow_pRank (R := (P : Subgroup G))
      (Quasithin.BlueprintB2.isElementaryAbelian_subgroupOf (Y := (P : Subgroup G)) hB)
    rwa [Quasithin.BlueprintB2.card_subgroupOf_eq hBP] at h
  set B := A₀.map π with hB
  have hBP : B ≤ Pb := by
    rw [hPb]
    exact map_mono hA₀P
  have hB1 : B ≠ ⊥ := by
    rw [hB, Ne, Subgroup.map_eq_bot_iff, hker]
    exact hAQ
  have hBea : IsElementaryAbelian p B := Quasithin.BlueprintB2.isElementaryAbelian_map hA₀ea π
  have hBp : IsPGroup p B := Pb.isPGroup'.to_le hBP
  set H₁ := ⁅B, H⁆ with hH₁
  have hH₁H : H₁ ≤ H := Subgroup.commutator_le_right B H
  have hBH₁ : B ≤ normalizer (H₁ : Set (G ⧸ Q)) := by
    intro b hb
    rw [mem_normalizer_iff_map_conj_eq, hH₁, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hb),
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top_iff.mpr hHn]; exact mem_top b)]
  have hH₁1 : H₁ ≠ ⊥ := by
    intro h
    apply hB1
    rw [eq_bot_iff, ← hfaith]
    exact le_inf hBP (commutator_eq_bot_iff_le_centralizer.mp h)
  have hHab : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x :=
    (Quasithin.BlueprintB2.isElementaryAbelian_iff.mp hHea).1
  have hcopBH : Nat.Coprime (Nat.card B) (Nat.card H) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
    rw [hk]
    exact Nat.Coprime.pow_left k hHc
  have hCH₁ : H₁ ⊓ centralizer (B : Set (G ⧸ Q)) = ⊥ :=
    commutator_inf_centralizer_eq_bot hHab
      (by rw [normalizer_eq_top_iff.mpr hHn]; exact le_top) hcopBH
  set L := (H₁ ⊔ B).comap π with hL
  set S := Q ⊔ A₀ with hS
  have hSP : S ≤ P := sup_le hQP hA₀P
  have hSp : IsPGroup p S := P.isPGroup'.to_le hSP
  have hSmap : S.map π = B := by
    have hQb : Q.map π = ⊥ := by rw [Subgroup.map_eq_bot_iff, hker]
    rw [hS, Subgroup.map_sup, hQb, bot_sup_eq]
  have hScomap : S = B.comap π := by
    rw [← hSmap, comap_map_eq, hker, sup_eq_left.mpr le_sup_left]
  have hSL : S ≤ L := by
    rw [hScomap, hL]
    exact comap_mono le_sup_right
  have hQL : Q ≤ L := le_sup_left.trans hSL
  have hNLS : L ⊓ normalizer (S : Set G) ≤ S := by
    intro x hx
    obtain ⟨hxL, hxN⟩ := mem_inf.mp hx
    have hxm : π x ∈ ((H₁ ⊔ B : Subgroup (G ⧸ Q)) : Set (G ⧸ Q)) := hxL
    rw [coe_mul_of_right_le_normalizer_left H₁ B hBH₁] at hxm
    obtain ⟨h, hh, b, hb, hhb⟩ := hxm
    dsimp only at hhb
    have hxB : π x ∈ normalizer (B : Set (G ⧸ Q)) := by
      rw [← hSmap]
      exact le_normalizer_map π (mem_map_of_mem π hxN)
    have hhB : h ∈ normalizer (B : Set (G ⧸ Q)) := by
      have heq : h = π x * b⁻¹ := by rw [← hhb, mul_inv_cancel_right]
      rw [heq]
      exact mul_mem hxB (inv_mem (le_normalizer hb))
    have hhC : h ∈ centralizer (B : Set (G ⧸ Q)) := by
      rw [mem_centralizer_iff]
      intro b' hb'
      have h1 : h * b' * h⁻¹ * b'⁻¹ ∈ B :=
        mul_mem ((mem_normalizer_iff.mp hhB b').mp hb') (inv_mem hb')
      have h2 : h * b' * h⁻¹ * b'⁻¹ ∈ H := by
        have h3 : h * (b' * h⁻¹ * b'⁻¹) ∈ H :=
          mul_mem (hH₁H hh) (hHn.conj_mem _ (inv_mem (hH₁H hh)) b')
        rwa [← mul_assoc, ← mul_assoc] at h3
      have h4 : h * b' * h⁻¹ * b'⁻¹ ∈ (Pb : Subgroup (G ⧸ Q)) ⊓ H := mem_inf.mpr ⟨hBP h1, h2⟩
      rw [SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hH Pb.isPGroup', mem_bot] at h4
      calc b' * h = (h * b' * h⁻¹ * b'⁻¹)⁻¹ * (h * b') := by group
        _ = h * b' := by rw [h4, inv_one, one_mul]
    have hh1 : h = 1 := by
      have h5 := mem_inf.mpr ⟨hh, hhC⟩
      rwa [hCH₁, mem_bot] at h5
    rw [hScomap, mem_comap, ← hhb, hh1, one_mul]
    exact hb
  have hSmax : ∀ S₂ : Subgroup G, IsPGroup p S₂ → S ≤ S₂ → S₂ ≤ L → S₂ = S := by
    intro S₂ hS₂ hSS₂ hS₂L
    by_contra hne
    have : Group.IsNilpotent S₂ := hS₂.isNilpotent
    have hlt := lt_inf_normalizer (lt_of_le_of_ne hSS₂ (Ne.symm hne))
    exact lt_irrefl _ (lt_of_lt_of_le hlt ((inf_le_inf_right _ hS₂L).trans hNLS))
  obtain ⟨S₁, hS₁⟩ := (hSp.comap_of_injective L.subtype L.subtype_injective).exists_le_sylow
  have hS₁eq : (S₁ : Subgroup L).map L.subtype = S :=
    hSmax _ (S₁.isPGroup'.map L.subtype) (fun x hx => ⟨⟨x, hSL hx⟩, hS₁ hx, rfl⟩)
      (map_subtype_le _)
  have hA₀J : A₀ ≤ 𝒥[p, S] := by
    have hA₀S : A₀ ≤ S := le_sup_right
    have hmem : A₀.subgroupOf S ∈ elemThompsonFamily S p := by
      rw [Quasithin.BlueprintB2.mem_elemThompsonFamily_iff]
      refine ⟨Quasithin.BlueprintB2.isElementaryAbelian_subgroupOf hA₀ea, fun B' hB' => ?_⟩
      rw [Quasithin.BlueprintB2.card_subgroupOf_eq hA₀S]
      have h := hAmax (B'.map S.subtype) ((map_subtype_le _).trans hSP)
        (Quasithin.BlueprintB2.isElementaryAbelian_map hB' _)
      rwa [card_map_of_injective S.subtype_injective] at h
    have h := map_mono (f := S.subtype) (le_sSup hmem : A₀.subgroupOf S ≤ elemThompson S p)
    rwa [map_subgroupOf_eq_of_le hA₀S] at h
  have hQJ : Q ⊔ 𝒥[p, S] = S :=
    le_antisymm (sup_le le_sup_left (map_subtype_le _))
      (sup_le le_sup_left (hA₀J.trans le_sup_right))
  have hNJS : L ⊓ normalizer (𝒥[p, S] : Set G) ≤ S := by
    refine le_trans (inf_le_inf_left _ fun x hx => ?_) hNLS
    rw [← hQJ, mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp hx,
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top_iff.mpr hQn]; exact mem_top x)]
  have hLtop : L = ⊤ := by
    by_contra hLne
    have hZS : 𝒵[(P : Subgroup G)] ≤ S := by
      intro z hz
      obtain ⟨-, hzc⟩ := mem_map_center_iff.mp hz
      exact (le_sup_left : Q ≤ S) (hCQ (mem_centralizer_iff.mpr fun y hy => hzc y (hQP hy)))
    have hC' : HasNormalPComplement p
        ↥(L ⊓ centralizer (𝒵[(S₁ : Subgroup L).map L.subtype] : Set G)) := by
      rw [hS₁eq]
      exact hasNormalPComplement_of_le p (inf_le_right.trans (centralizer_center_le hSP hZS)) M.hC
    have hN' : HasNormalPComplement p
        ↥(L ⊓ normalizer (𝒥[p, (S₁ : Subgroup L).map L.subtype] : Set G)) := by
      rw [hS₁eq]
      exact BenderSuzuki.External.hkt_hasNormalPComplement_of_isPGroup (hSp.to_le hNJS)
    have hLp := hpgrp L hQL (M.hnc_of_lt L hLne S₁ hC' hN')
    apply hH₁1
    have hH₁L : H₁ ≤ L.map π := by
      rw [hL, map_comap_eq_self_of_surjective hπs]
      exact le_sup_left
    have hH₁p : IsPGroup p H₁ := (hLp.map π).to_le hH₁L
    rw [eq_bot_iff, ← SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hH hH₁p]
    exact le_inf le_rfl hH₁H
  have hPS : (P : Subgroup G) = S := hSmax P P.isPGroup' hSP (by rw [hLtop]; exact le_top)
  have hPbB : (Pb : Subgroup (G ⧸ Q)) = B := by rw [hPb, hPS, hSmap]
  have hPbcard : Nat.card (Pb : Subgroup (G ⧸ Q)) = p := by
    rw [hPbB]
    have := hBea
    exact card_eq_prime_of_irreducible hB1 hH hH1
      (fun K hKH hBK => eq_bot_or_eq_of_le_normalizer Pb hH hmax hKH (by rw [hPbB]; exact hBK))
      (by rw [← hPbB]; exact hfaith)
  have := hA₀ea
  have := hHea
  refine SteinbergBS.maximal_elementary_sylow_prime_quotient_obstruction hp2 hqp P Q hQp hCQ H
    (by rw [← hPb]; exact hPbcard) ?_ ?_ A₀ hAmax hPS.symm M.hC
  · intro hle
    apply hB1
    rw [eq_bot_iff, ← hfaith]
    exact le_inf hBP (hPb ▸ hle |>.trans' hBP)
  · intro K hKH hPK
    exact eq_bot_or_eq_of_le_normalizer Pb hH hmax hKH (by rw [hPb]; exact hPK)

end ThompsonMinimal

theorem thompson_elementary_normal_p_complement {G : Type u} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (P : Sylow p G)
    (hC : HasNormalPComplement p ↥(centralizer
      (((center (P : Subgroup G)).map (P : Subgroup G).subtype : Subgroup G) : Set G)))
    (hN : HasNormalPComplement p ↥(normalizer
      (((elemThompson (P : Subgroup G) p).map (P : Subgroup G).subtype : Subgroup G) : Set G))) :
    HasNormalPComplement p G := by
  suffices key : ∀ (n : ℕ) (G : Type u) [Group G] [Finite G], Nat.card G = n →
      ∀ P : Sylow p G,
        HasNormalPComplement p ↥(centralizer (𝒵[(P : Subgroup G)] : Set G)) →
        HasNormalPComplement p ↥(normalizer (𝒥[p, (P : Subgroup G)] : Set G)) →
        HasNormalPComplement p G from key _ G rfl P hC hN
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn P hC hN
  by_contra hG
  exact ThompsonMinimal.false_of_minimal hp2
    ⟨hC, hN, hG, fun H _ _ hH S hCS hNS => ih _ (hn ▸ hH) H rfl S hCS hNS⟩

end Minimal

end CFSG.RankThree.Coprime
