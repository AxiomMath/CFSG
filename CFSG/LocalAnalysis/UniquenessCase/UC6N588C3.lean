module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588C2
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Walter.Bender1970.S2.Layer
public import CFSG.LocalAnalysis.UniquenessCase.UC6Grp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.N588

open Subgroup
open scoped commutatorElement
open CFSG.GorensteinWalter (IsComponentOf generalizedFittingSubgroupOf componentLayerOf)

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_le_fstar (X : Subgroup G) :
    X ⊓ centralizer (generalizedFittingSubgroupOf X : Set G) ≤ generalizedFittingSubgroupOf X := by
  rintro x ⟨hxX, hxC⟩
  rw [← CFSG.GorensteinWalter.generalizedFittingSubgroupOf_subgroup_top_eq X]
  refine ⟨⟨x, hxX⟩, CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le (G := X) ?_,
    rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hy' : (y : G) ∈ generalizedFittingSubgroupOf X := by
    rw [← CFSG.GorensteinWalter.generalizedFittingSubgroupOf_subgroup_top_eq X]
    exact ⟨y, hy, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp hxC) y hy'

theorem commutator_eq_bot_of_fitting_of_components {X L : Subgroup G}
    (hLX : L ≤ normalizer (X : Set G)) (hLperf : ⁅L, L⁆ = L)
    (hF : L ≤ centralizer (CFSG.fittingSubgroupOf X : Set G))
    (hE : ∀ K : Subgroup G, IsComponentOf K X → L ≤ centralizer (K : Set G)) : ⁅X, L⁆ = ⊥ := by
  set F := generalizedFittingSubgroupOf X with hFdef
  have hFL : F ≤ centralizer (L : Set G) := by
    refine sup_le (Subgroup.le_centralizer_iff.1 hF) ?_
    exact sSup_le fun K hK => Subgroup.le_centralizer_iff.1 (hE K hK)
  have hFLb : ⁅F, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hFL
  have hFn := CFSG.GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn X
  have hFX : ⁅F, X⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro f hf x hx
    have h1 : x * f⁻¹ * x⁻¹ ∈ F := hFn.2 x hx _ (F.inv_mem hf)
    rw [commutatorElement_def, show f * x * f⁻¹ * x⁻¹ = f * (x * f⁻¹ * x⁻¹) by group]
    exact F.mul_mem hf h1
  have h1 : ⁅⁅L, F⁆, X⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L F, hFLb, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅F, X⁆, L⁆ = ⊥ :=
    eq_bot_iff.2 ((Subgroup.commutator_mono hFX le_rfl).trans hFLb.le)
  have h3 : ⁅⁅X, L⁆, F⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have h4 : ⁅X, L⁆ ≤ F := by
    refine le_trans (le_inf (commutator_le_of_le_normalizer hLX)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)) (inf_centralizer_le_fstar X)
  refine commutator_eq_bot_of_perfect hLperf (eq_bot_iff.2 ?_)
  exact (Subgroup.commutator_mono h4 le_rfl).trans hFLb.le


theorem eq_one_of_perfect_of_isSolvable {A B : Type*} [Group A] [Group B] [Group.IsSolvable B]
    (hA : commutator A = ⊤) (f : A →* B) : f = 1 := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := B)
  have h1 : ∀ m, derivedSeries A m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih]; exact hA
  refine MonoidHom.ext fun x => ?_
  have hx : f x ∈ derivedSeries B n :=
    map_derivedSeries_le_derivedSeries f n ⟨x, (h1 n).symm ▸ mem_top x, rfl⟩
  rw [hn, mem_bot] at hx
  simpa using hx

theorem commutator_eq_top_of_perfect {L : Subgroup G} (h : ⁅L, L⁆ = L) : commutator ↥L = ⊤ := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_self_eq_of_perfect {K : Subgroup G} (h : commutator ↥K = ⊤) : ⁅K, K⁆ = K := by
  rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem not_comm_quot_center {K : Type*} [Group K] (hK : CFSG.GorensteinWalter.IsQuasisimple K) :
    ¬ ∀ a b : K ⧸ center K, a * b = b * a := by
  obtain ⟨-, hperf, hsimple⟩ := hK
  intro h
  have hle : commutator K ≤ center K := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (center K) ⁅a, b⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h _ _
  rw [hperf, top_le_iff] at hle
  haveI : Nontrivial (K ⧸ center K) := hsimple.toNontrivial
  obtain ⟨u, v, huv⟩ := exists_pair_ne (K ⧸ center K)
  apply huv
  induction u using QuotientGroup.induction_on with | H u =>
  induction v using QuotientGroup.induction_on with | H v =>
  rw [QuotientGroup.eq, hle]
  exact mem_top _


theorem center_quot_center_eq_bot {K : Type*} [Group K]
    (hK : CFSG.GorensteinWalter.IsQuasisimple K) : center (K ⧸ center K) = ⊥ := by
  haveI : IsSimpleGroup (K ⧸ center K) := hK.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (K ⧸ center K)) with h | h
  · exact h
  · exfalso
    refine not_comm_quot_center hK fun a b => ?_
    exact ((Subgroup.mem_center_iff.1 (h ▸ mem_top b)) a)

theorem le_centralizer_of_forall_mk_eq {K L : Subgroup G} (hK : commutator ↥K = ⊤)
    (hLK : L ≤ normalizer (K : Set G))
    (h : ∀ (ℓ : ↥L) (k : ↥K),
      ((K.normalizerMonoidHom ⟨ℓ, hLK ℓ.2⟩ k : ↥K) : ↥K ⧸ center ↥K) = (k : ↥K ⧸ center ↥K)) :
    L ≤ centralizer (K : Set G) := by
  set ZK : Subgroup G := (center ↥K).map K.subtype with hZK
  have hcomm : ⁅K, L⁆ ≤ ZK := by
    rw [Subgroup.commutator_le]
    intro k hk ℓ hℓ
    have h1 := h ⟨ℓ, hℓ⟩ ⟨k, hk⟩⁻¹
    rw [QuotientGroup.eq] at h1
    refine ⟨_, (center ↥K).inv_mem h1, ?_⟩
    simp only [Subgroup.coe_subtype, mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def]
    group
  have hZc : ZK ≤ centralizer (K : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨k, hk⟩)
  have h1 : ⁅⁅K, L⁆, K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hcomm.trans hZc)
  have h2 : ⁅⁅L, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm L K]; exact h1
  have h3 : ⁅⁅K, K⁆, L⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [commutator_self_eq_of_perfect hK] at h3
  exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)

theorem exists_inner_of_schreier (hSch : UCK.KSch) {K L : Subgroup G}
    (hK : CFSG.GorensteinWalter.IsQuasisimple ↥K) (hKk : CFSG.Open.IsKGroup ↥K)
    (hLK : L ≤ normalizer (K : Set G)) (hLperf : ⁅L, L⁆ = L) :
    ∃ φ : ↥L →* ↥K ⧸ center ↥K, ∀ (ℓ : ↥L) (k : ↥K),
      ((K.normalizerMonoidHom ⟨ℓ, hLK ℓ.2⟩ k : ↥K) : ↥K ⧸ center ↥K) =
        φ ℓ * (k : ↥K ⧸ center ↥K) * (φ ℓ)⁻¹ := by
  haveI : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2.2
  have hZS := center_quot_center_eq_bot hK
  have hinj : Function.Injective (MulAut.conj : ↥K ⧸ center ↥K →* MulAut (↥K ⧸ center ↥K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    rw [← hZS, Subgroup.mem_center_iff]
    intro t
    have h1 := congrArg (fun e : MulAut (↥K ⧸ center ↥K) => e t) hs
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc t * s = (s * t * s⁻¹) * s := by rw [h1]
      _ = s * t := by group
  let σ : ↥L →* MulAut (↥K ⧸ center ↥K) :=
    (autQuot (center ↥K)).comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hLK))
  have hKS : CFSG.Open.IsKGroup (↥K ⧸ center ↥K) := hKk.quotient (center ↥K)
  haveI : Group.IsSolvable (MulAut (↥K ⧸ center ↥K) ⧸
      (MulAut.conj : ↥K ⧸ center ↥K →* MulAut (↥K ⧸ center ↥K)).range) :=
    hSch _ inferInstance hKS
  have hτ := eq_one_of_perfect_of_isSolvable (commutator_eq_top_of_perfect hLperf)
    ((QuotientGroup.mk'
      (MulAut.conj : ↥K ⧸ center ↥K →* MulAut (↥K ⧸ center ↥K)).range).comp σ)
  have hσ : ∀ ℓ, σ ℓ ∈ (MulAut.conj : ↥K ⧸ center ↥K →* MulAut (↥K ⧸ center ↥K)).range := by
    intro ℓ
    have h1 := congrArg (fun f : ↥L →* MulAut (↥K ⧸ center ↥K) ⧸
      (MulAut.conj : ↥K ⧸ center ↥K →* MulAut (↥K ⧸ center ↥K)).range => f ℓ) hτ
    simp only [MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
      MonoidHom.one_apply] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  let φ : ↥L →* ↥K ⧸ center ↥K :=
    ((MonoidHom.ofInjective hinj).symm : _ →* ↥K ⧸ center ↥K).comp (σ.codRestrict _ hσ)
  have hφ : ∀ ℓ, MulAut.conj (φ ℓ) = σ ℓ := by
    intro ℓ
    have h1 := MonoidHom.ofInjective_apply hinj (x := φ ℓ)
    have h2 : MonoidHom.ofInjective hinj (φ ℓ) = σ.codRestrict _ hσ ℓ := by
      simp [φ]
    rw [h2] at h1
    exact h1.symm.trans rfl
  refine ⟨φ, fun ℓ k => ?_⟩
  have h1 := congrArg (fun e : MulAut (↥K ⧸ center ↥K) => e (k : ↥K ⧸ center ↥K)) (hφ ℓ)
  simp only [MulAut.conj_apply] at h1
  rw [h1]
  rfl


theorem le_centralizer_of_coprime (hSch : UCK.KSch) {r : ℕ} {K L : Subgroup G}
    (hK : CFSG.GorensteinWalter.IsQuasisimple ↥K) (hKk : CFSG.Open.IsKGroup ↥K)
    (hLK : L ≤ normalizer (K : Set G)) (hLperf : ⁅L, L⁆ = L)
    (hLgen : ∀ T : Subgroup G, (∀ ℓ ∈ L, (∃ a : ℕ, orderOf ℓ = r ^ a) → ℓ ∈ T) → L ≤ T)
    (hcop : Nat.Coprime r (Nat.card K)) : L ≤ centralizer (K : Set G) := by
  obtain ⟨φ, hφ⟩ := exists_inner_of_schreier hSch hK hKk hLK hLperf
  have hT : L ≤ φ.ker.map L.subtype := by
    refine hLgen _ fun ℓ hℓ ⟨a, ha⟩ => ⟨⟨ℓ, hℓ⟩, (MonoidHom.mem_ker).2 ?_, rfl⟩
    rw [← orderOf_eq_one_iff]
    have h1 : orderOf (φ ⟨ℓ, hℓ⟩) ∣ r ^ a := by
      rw [← ha, ← Subgroup.orderOf_mk ℓ hℓ]
      exact orderOf_map_dvd φ _
    have h2 : orderOf (φ ⟨ℓ, hℓ⟩) ∣ Nat.card K :=
      (_root_.orderOf_dvd_natCard _).trans (Subgroup.card_quotient_dvd_card _)
    exact Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left a hcop) h1 h2
  refine le_centralizer_of_forall_mk_eq hK.2.1 hLK fun ℓ k => ?_
  have h1 : φ ℓ = 1 := by
    obtain ⟨ℓ', hℓ', hℓ'e⟩ := hT ℓ.2
    have : ℓ' = ℓ := Subtype.ext hℓ'e
    rw [← this]
    exact hℓ'
  rw [hφ, h1, one_mul, inv_one, mul_one]

theorem not_isCyclic_of_elemAbelian {r : ℕ} (hr : r.Prime) {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian r B) (hBc : Nat.card B = r ^ 2) : ¬ IsCyclic B := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have h1 : orderOf g = Nat.card B := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ r = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hB.2 g g.2)
  have h3 : r ^ 2 ∣ r := by
    rw [← hBc, ← h1]
    exact orderOf_dvd_of_pow_eq_one h2
  have h4 := Nat.le_of_dvd hr.pos h3
  have h5 : r < r ^ 2 := by
    calc r = r ^ 1 := (pow_one r).symm
      _ < r ^ 2 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
  omega

theorem le_centralizer_of_cyclic (hSch : UCK.KSch) {r : ℕ} [hr : Fact r.Prime]
    {K L B : Subgroup G} (hK : CFSG.GorensteinWalter.IsQuasisimple ↥K)
    (hKk : CFSG.Open.IsKGroup ↥K) (hLK : L ≤ normalizer (K : Set G)) (hLperf : ⁅L, L⁆ = L)
    (hLs : IsSimpleGroup ↥L) (hBL : B ≤ L) (hB : CFSG.Open.IsElemAbelian r B)
    (hBc : Nat.card B = r ^ 2)
    (hcyc : ∀ D : Subgroup G, D ≤ K → IsPGroup r D → IsCyclic D) :
    L ≤ centralizer (K : Set G) := by
  obtain ⟨φ, hφ⟩ := exists_inner_of_schreier hSch hK hKk hLK hLperf
  have h1 : φ = 1 := by
    by_contra hne
    have hker : φ.ker = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
      · exact h
      · exact absurd (MonoidHom.ext fun x => (φ.mem_ker).1 (h ▸ mem_top x)) hne
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
    set B' : Subgroup ↥L := B.subgroupOf L
    have hB'p : IsPGroup r B' := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hBc]
    obtain ⟨P, hP⟩ := (hB'p.map φ).exists_le_sylow
    obtain ⟨D⟩ := (inferInstance : Nonempty (Sylow r ↥K))
    have hDc : IsCyclic (D : Subgroup ↥K) := by
      have h1 := hcyc ((D : Subgroup ↥K).map K.subtype) (Subgroup.map_subtype_le _)
        (D.isPGroup'.map K.subtype)
      exact (MulEquiv.isCyclic ((D : Subgroup ↥K).equivMapOfInjective K.subtype
        K.subtype_injective)).2 h1
    set D' := D.mapSurjective (QuotientGroup.mk'_surjective (center ↥K)) with hD'
    have hD'c : IsCyclic (D' : Subgroup (↥K ⧸ center ↥K)) := by
      rw [hD', Sylow.coe_mapSurjective]
      exact isCyclic_of_surjective ((QuotientGroup.mk' (center ↥K)).subgroupMap _)
        (MonoidHom.subgroupMap_surjective _ _)
    have hPc : IsCyclic (P : Subgroup (↥K ⧸ center ↥K)) :=
      (MulEquiv.isCyclic (Sylow.equiv P D')).2 hD'c
    have hBφ : IsCyclic (B'.map φ) := Subgroup.isCyclic_of_le hP
    have hB'c : IsCyclic B' := (MulEquiv.isCyclic (B'.equivMapOfInjective φ hinj)).2 hBφ
    have hBcyc : IsCyclic B :=
      (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hBL)).1 hB'c
    exact not_isCyclic_of_elemAbelian hr.out hB hBc hBcyc
  refine le_centralizer_of_forall_mk_eq hK.2.1 hLK fun ℓ k => ?_
  rw [hφ, h1, MonoidHom.one_apply, one_mul, inv_one, mul_one]


theorem elemAbelian_sup_zpowers {q : ℕ} [hq : Fact q.Prime] {E : Subgroup G}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEq : ∀ a ∈ E, a ^ q = 1) {y : G} (hyE : y ∉ E)
    (hyq : y ^ q = 1) (hyc : ∀ a ∈ E, a * y = y * a) :
    (∀ a ∈ E ⊔ zpowers y, ∀ b ∈ E ⊔ zpowers y, a * b = b * a) ∧
      (∀ a ∈ E ⊔ zpowers y, a ^ q = 1) ∧ Nat.card ↥(E ⊔ zpowers y) = Nat.card E * q := by
  have hy1 : y ≠ 1 := fun h => hyE (h ▸ E.one_mem)
  have hyC : y ∈ centralizer (E : Set G) := mem_centralizer_iff.2 hyc
  have hEC : E ≤ centralizer (E : Set G) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => hEc b hb a ha
  have hyy : y ∈ centralizer ((zpowers y : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (Commute.refl y) k).eq
  have h1 : E ⊔ zpowers y ≤ centralizer (E : Set G) := sup_le hEC ((zpowers_le).2 hyC)
  have h2 : E ⊔ zpowers y ≤ centralizer ((zpowers y : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.1 ((zpowers_le).2 hyC)) ((zpowers_le).2 hyy)
  have hcent : E ⊔ zpowers y ≤ centralizer ((E ⊔ zpowers y : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.1 h1) (Subgroup.le_centralizer_iff.1 h2)
  have hcomm : ∀ a ∈ E ⊔ zpowers y, ∀ b ∈ E ⊔ zpowers y, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (hcent hb) a ha
  have hyord : orderOf y = q := orderOf_eq_prime hyq hy1
  refine ⟨hcomm, fun a ha => ?_, ?_⟩
  · have key : a ∈ E ⊔ zpowers y ∧ a ^ q = 1 := by
      rw [Subgroup.sup_eq_closure] at ha
      induction ha using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact ⟨mem_sup_left hx, hEq x hx⟩
        · refine ⟨mem_sup_right hx, ?_⟩
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyq, one_zpow]
      | one => exact ⟨one_mem _, one_pow q⟩
      | mul a b _ _ ha hb =>
        exact ⟨mul_mem ha.1 hb.1, by
          rw [(Commute.mul_pow (hcomm a ha.1 b hb.1)), ha.2, hb.2, one_mul]⟩
      | inv a _ ha => exact ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩
    exact key.2
  · have hd : E ⊓ zpowers y = ⊥ := by
      have hcard : Nat.card (zpowers y) = q := by rw [Nat.card_zpowers, hyord]
      have hdvd : Nat.card ↥(E ⊓ zpowers y) ∣ q :=
        hcard ▸ Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime hq.out).1 hdvd with h | h
      · exact Subgroup.card_eq_one.1 h
      · exfalso
        have heq : E ⊓ zpowers y = zpowers y :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcard])
        have hy' : y ∈ E ⊓ zpowers y := by rw [heq]; exact mem_zpowers y
        exact hyE hy'.1
    rw [card_sup_of_commute_of_disjoint (fun a ha b hb => ?_) hd, Nat.card_zpowers, hyord]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hyc a ha) k).eq


theorem exists_odd_prime_dvd_card_quot {K : Type*} [Group K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsQuasisimple K) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card (K ⧸ center K) := by
  by_contra hcon
  push Not at hcon
  haveI : Nontrivial (K ⧸ center K) := hK.2.2.toNontrivial
  have h2 : IsPGroup 2 (K ⧸ center K) := by
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdc => by
      by_contra hne
      exact hcon d hd hne hdc⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := h2.center_nontrivial
  rw [center_quot_center_eq_bot hK] at hZ
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hZ rfl

theorem mem_normalizer_of_pRank_le_three {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    {O K : Subgroup G} (hK : IsComponentOf K O) {ℓ : G} (hℓO : ℓ ∈ normalizer (O : Set G))
    {a : ℕ} (hℓr : orderOf ℓ = r ^ a)
    (hz : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → ℓ * z * ℓ⁻¹ = z)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q O ≤ 3) :
    ℓ ∈ normalizer (K : Set G) := by
  by_contra hℓK
  set C : ℕ → Subgroup G := fun i => K.map (MulAut.conj (ℓ ^ i)).toMonoidHom with hC
  have hCc : ∀ i, IsComponentOf (C i) O := fun i =>
    CFSG.Walter.isComponentOf_map_conj hK (Subgroup.pow_mem _ hℓO i)
  have hmemC : ∀ i, ∀ k ∈ K, ℓ ^ i * k * (ℓ ^ i)⁻¹ ∈ C i := fun i k hk => ⟨k, hk, rfl⟩
  have hne : ∀ i j : ℕ, i < j → j ≤ 4 → C i ≠ C j := by
    intro i j hij hj4 heq
    have hnorm : ℓ ^ (j - i) ∈ normalizer (K : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun k hk => ?_
      have h1 : ℓ ^ j * k * (ℓ ^ j)⁻¹ ∈ C i := heq ▸ hmemC j k hk
      obtain ⟨y, hy, hyk⟩ := h1
      have hy' : ℓ ^ i * y * (ℓ ^ i)⁻¹ = ℓ ^ j * k * (ℓ ^ j)⁻¹ := hyk
      have hj : ℓ ^ j = ℓ ^ i * ℓ ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hij.le]
      have : ℓ ^ (j - i) * k * (ℓ ^ (j - i))⁻¹ = y := by
        calc ℓ ^ (j - i) * k * (ℓ ^ (j - i))⁻¹
            = (ℓ ^ i)⁻¹ * (ℓ ^ i * ℓ ^ (j - i) * k * (ℓ ^ i * ℓ ^ (j - i))⁻¹) * ℓ ^ i := by
              group
          _ = (ℓ ^ i)⁻¹ * (ℓ ^ i * y * (ℓ ^ i)⁻¹) * ℓ ^ i := by rw [← hj, hy']
          _ = y := by group
      rw [this]
      exact hy
    have hcop : (j - i).gcd (orderOf ℓ) = 1 := by
      rw [hℓr]
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_of_lt_prime (by omega) (by omega) hr).symm
    exact hℓK ((zpowers_le.2 hnorm) (mem_zpowers_pow_iff.2 hcop))
  have hcomm : ∀ i j, i ≤ 4 → j ≤ 4 → i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x * y = y * x := by
    intro i j hi hj hij x hx y hy
    rcases CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot (hCc i) (hCc j) with h | h
    · rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
      · exact absurd h (hne i j hlt hj)
      · exact absurd h.symm (hne j i hlt hi)
    · have hm : x * y * x⁻¹ * y⁻¹ = 1 := by
        rw [← commutatorElement_def, ← mem_bot, ← h]
        exact commutator_mem_commutator hx hy
      calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
        _ = y * x := by rw [hm, one_mul]
  obtain ⟨q, hq, hq2, hqd⟩ := exists_odd_prime_dvd_card_quot hK.2.2
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨xbar, hxbar⟩ := exists_prime_orderOf_dvd_card' q hqd
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xbar
  set x : G := (x₀ : G) with hxdef
  have hxK : x ∈ K := x₀.2
  have hxnc : ¬ ∀ k ∈ K, x * k = k * x := by
    intro h
    have h1 : x₀ ∈ center ↥K := Subgroup.mem_center_iff.2 fun k =>
      Subtype.ext (h k k.2).symm
    have h2 : ((x₀ : ↥K) : ↥K ⧸ center ↥K) = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [h2, orderOf_one] at hxbar
    exact hq.one_lt.ne hxbar
  have hxq : ∀ k ∈ K, x ^ q * k = k * x ^ q := by
    have h1 : ((x₀ ^ q : ↥K) : ↥K ⧸ center ↥K) = 1 := by
      rw [QuotientGroup.mk_pow, ← hxbar, pow_orderOf_eq_one]
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    intro k hk
    have h3 := congrArg Subtype.val ((Subgroup.mem_center_iff.1 h2) ⟨k, hk⟩)
    simpa using h3.symm
  have hxqℓ : ∀ i : ℕ, ℓ ^ i * x ^ q * (ℓ ^ i)⁻¹ = x ^ q := by
    have h1 : ℓ * x ^ q * ℓ⁻¹ = x ^ q := hz _ (K.pow_mem hxK q) hxq
    have h2 : Commute ℓ (x ^ q) := by
      calc ℓ * x ^ q = (ℓ * x ^ q * ℓ⁻¹) * ℓ := by group
        _ = x ^ q * ℓ := by rw [h1]
    intro i
    rw [((h2.pow_left i).eq), mul_assoc, mul_inv_cancel, mul_one]
  set xs : ℕ → G := fun i => ℓ ^ i * x * (ℓ ^ i)⁻¹ with hxs
  have hxsC : ∀ i, xs i ∈ C i := fun i => hmemC i x hxK
  have hxs0 : xs 0 = x := by simp [hxs]
  have hxspow : ∀ i, xs i ^ q = x ^ q := fun i => by rw [hxs, conj_pow, hxqℓ]
  have hxsnc : ∀ i, ¬ ∀ k ∈ C i, xs i * k = k * xs i := by
    intro i h
    apply hxnc
    intro k hk
    have h1 := h _ (hmemC i k hk)
    have h2 : ℓ ^ i * (x * k) * (ℓ ^ i)⁻¹ = ℓ ^ i * (k * x) * (ℓ ^ i)⁻¹ := by
      rw [show ℓ ^ i * (x * k) * (ℓ ^ i)⁻¹ = xs i * (ℓ ^ i * k * (ℓ ^ i)⁻¹) by rw [hxs]; group,
        h1]
      rw [hxs]; group
    have h3 := congrArg (fun t => (ℓ ^ i)⁻¹ * t * ℓ ^ i) h2
    simpa [mul_assoc] using h3
  have hxscomm : ∀ i j, i ≤ 4 → j ≤ 4 → xs i * xs j = xs j * xs i := by
    intro i j hi hj
    by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hi hj hij _ (hxsC i) _ (hxsC j)
  set ys : ℕ → G := fun j => xs j * (xs 0)⁻¹ with hys
  have hysq : ∀ j, j ≤ 4 → ys j ^ q = 1 := by
    intro j hj
    have hc : Commute (xs j) (xs 0)⁻¹ := (Commute.inv_right (hxscomm j 0 hj (by omega)))
    rw [hys, hc.mul_pow, inv_pow, hxspow, hxspow, mul_inv_cancel]
  have hyscomm : ∀ i j, i ≤ 4 → j ≤ 4 → ys i * ys j = ys j * ys i := by
    intro i j hi hj
    have c1 : Commute (xs i) (xs j) := hxscomm i j hi hj
    have c2 : Commute (xs i) (xs 0)⁻¹ := Commute.inv_right (hxscomm i 0 hi (by omega))
    have c3 : Commute (xs 0)⁻¹ (xs j) := Commute.inv_left (hxscomm 0 j (by omega) hj)
    have c4 : Commute (xs 0)⁻¹ (xs 0)⁻¹ := Commute.refl _
    exact ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq
  set J : ℕ → Subgroup G := fun j => ⨆ (i : ℕ) (_ : i ≤ j), C i with hJ
  have hCJ : ∀ i j, i ≤ j → C i ≤ J j := fun i j h => le_iSup₂_of_le i h le_rfl
  have hJO : ∀ j, J j ≤ O := fun j => iSup₂_le fun i _ => (hCc i).1
  have hJmono : ∀ i j, i ≤ j → J i ≤ J j := fun i j h =>
    iSup₂_le fun k hk => hCJ k j (hk.trans h)
  have hysJ : ∀ j, ys j ∈ J j := fun j =>
    mul_mem (hCJ j j le_rfl (hxsC j)) (inv_mem (hCJ 0 j (Nat.zero_le _) (hxsC 0)))
  have hysnotJ : ∀ j, j + 1 ≤ 4 → ys (j + 1) ∉ J j := by
    intro j hj hmem
    have hcent : J j ≤ centralizer ((C (j + 1) : Subgroup G) : Set G) :=
      iSup₂_le fun i hi => fun y hy => mem_centralizer_iff.2 fun k hk =>
        (hcomm i (j + 1) (by omega) hj (by omega) y hy k hk).symm
    have hx1 : xs (j + 1) ∈ J j := by
      have : xs (j + 1) = ys (j + 1) * xs 0 := by rw [hys]; group
      rw [this]
      exact mul_mem hmem (hCJ 0 j (Nat.zero_le _) (hxsC 0))
    exact hxsnc (j + 1) fun k hk => (mem_centralizer_iff.1 (hcent hx1) k hk).symm
  set E : ℕ → Subgroup G := fun j => ⨆ (i : ℕ) (_ : 1 ≤ i ∧ i ≤ j), zpowers (ys i) with hE
  have hE0 : E 0 = ⊥ := by
    rw [hE, eq_bot_iff]
    exact iSup₂_le fun i hi => by omega
  have hEsucc : ∀ j, E (j + 1) = E j ⊔ zpowers (ys (j + 1)) := by
    intro j
    apply le_antisymm
    · refine iSup₂_le fun i hi => ?_
      by_cases h : i = j + 1
      · rw [h]; exact le_sup_right
      · exact le_sup_of_le_left (le_iSup₂_of_le i ⟨hi.1, by omega⟩ le_rfl)
    · exact sup_le (iSup₂_le fun i hi => le_iSup₂_of_le i ⟨hi.1, by omega⟩ le_rfl)
        (le_iSup₂_of_le (j + 1) ⟨by omega, le_rfl⟩ le_rfl)
  have hEJ : ∀ j, E j ≤ J j := fun j =>
    iSup₂_le fun i hi => (zpowers_le).2 (hJmono i j hi.2 (hysJ i))
  have hEcent : ∀ j m, j ≤ 4 → m ≤ 4 → ∀ b ∈ E j, b * ys m = ys m * b := by
    intro j m hj hm b hb
    have hle : E j ≤ centralizer ({ys m} : Set G) := iSup₂_le fun i hi =>
      (zpowers_le).2 (mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (hyscomm i m (by omega) hm).symm)
    exact (mem_centralizer_iff.1 (hle hb) (ys m) rfl).symm
  have hind : ∀ j, j ≤ 4 → (∀ a ∈ E j, ∀ b ∈ E j, a * b = b * a) ∧ (∀ a ∈ E j, a ^ q = 1) ∧
      Nat.card (E j) = q ^ j := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [hE0]
      refine ⟨fun a ha b hb => ?_, fun a ha => ?_, by simp⟩
      · rw [mem_bot] at ha hb; rw [ha, hb]
      · rw [mem_bot] at ha; rw [ha, one_pow]
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have hyE : ys (j + 1) ∉ E j := fun h => hysnotJ j hj (hEJ j h)
      obtain ⟨k1, k2, k3⟩ := elemAbelian_sup_zpowers h1 h2 hyE (hysq (j + 1) hj)
        (hEcent j (j + 1) (by omega) hj)
      rw [hEsucc]
      exact ⟨k1, k2, by rw [k3, h3, pow_succ]⟩
  obtain ⟨h1, h2, h3⟩ := hind 4 le_rfl
  have hel : CFSG.Open.IsElemAbelian q (E 4) :=
    ⟨⟨⟨fun u v => Subtype.ext (h1 u u.2 v v.2)⟩⟩, h2⟩
  have hle : 4 ≤ CFSG.Open.pRank q O :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove q hq O)
      ⟨E 4, (hEJ 4).trans (hJO 4), hel, h3⟩
  have := hrank q hq hq2
  omega


theorem false_of_sylow_le_of_commutator_eq_bot {r : ℕ} [Fact r.Prime] {X A B : Subgroup G}
    (hA : IsComponentOf A X) (hAB : ⁅A, B⁆ = ⊥) (hdA : r ∣ Nat.card A) (P : Sylow r ↥A)
    (hPB : (P : Subgroup ↥A).map A.subtype ≤ B) : False := by
  have hPc : (P : Subgroup ↥A) ≤ center ↥A := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxB : (x : G) ∈ B := hPB ⟨x, hx, rfl⟩
    have h1 : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ = 1 := by
      rw [← commutatorElement_def, ← mem_bot, ← hAB]
      exact commutator_mem_commutator y.2 hxB
    calc ((y * x : ↥A) : G) = (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ * (x * y) := by
          rw [Subgroup.coe_mul]; group
      _ = ((x * y : ↥A) : G) := by rw [h1, one_mul, Subgroup.coe_mul]
  have hN : normalizer ((P : Subgroup ↥A) : Set ↥A) ≤ centralizer ((P : Subgroup ↥A) : Set ↥A) :=
    fun g _ => mem_centralizer_iff.2 fun h hh => (Subgroup.mem_center_iff.1 (hPc hh) g).symm
  haveI : IsMulCommutative (P : Subgroup ↥A) :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 (hPc a.2) b).symm)⟩⟩
  have htriv := eq_one_of_perfect_of_isSolvable hA.2.2.2.1 (MonoidHom.transferSylow P hN)
  have hker : (MonoidHom.transferSylow P hN).ker = ⊤ := by rw [htriv]; exact MonoidHom.ker_one
  have h2 := MonoidHom.not_dvd_card_ker_transferSylow P hN
  rw [hker, Subgroup.card_top] at h2
  exact h2 hdA

theorem eq_of_isComponentOf_of_dvd {r : ℕ} [hr : Fact r.Prime] {X K₁ K₂ : Subgroup G}
    (h₁ : IsComponentOf K₁ X) (h₂ : IsComponentOf K₂ X) (hd₁ : r ∣ Nat.card K₁)
    (hd₂ : r ∣ Nat.card K₂) (hcyc : ∀ D : Subgroup G, D ≤ X → IsPGroup r D → IsCyclic D) :
    K₁ = K₂ := by
  by_contra hne
  have hc : ⁅K₁, K₂⁆ = ⊥ :=
    (CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot h₁ h₂).resolve_left hne
  obtain ⟨P₁⟩ := (inferInstance : Nonempty (Sylow r ↥K₁))
  obtain ⟨P₂⟩ := (inferInstance : Nonempty (Sylow r ↥K₂))
  set D₁ := (P₁ : Subgroup ↥K₁).map K₁.subtype with hD₁def
  set D₂ := (P₂ : Subgroup ↥K₂).map K₂.subtype with hD₂def
  have hD₁K : D₁ ≤ K₁ := map_subtype_le _
  have hD₂K : D₂ ≤ K₂ := map_subtype_le _
  have hD₁ : IsPGroup r D₁ := P₁.isPGroup'.map _
  have hD₂ : IsPGroup r D₂ := P₂.isPGroup'.map _
  have hD₁N : D₁ ≤ normalizer (D₂ : Set G) := by
    intro x hx
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [← commutatorElement_def, ← mem_bot, ← hc]
      exact commutator_mem_commutator (hD₁K hx) (hD₂K hy)
    calc y * x = x * y * x⁻¹ * y⁻¹ * (y * x) := by rw [h1, one_mul]
      _ = x * y := by group
  have hCp : IsPGroup r (D₁ ⊔ D₂ : Subgroup G) := hD₁.to_sup_of_normal_right' hD₂ hD₁N
  have hCX : D₁ ⊔ D₂ ≤ X := sup_le (hD₁K.trans h₁.1) (hD₂K.trans h₂.1)
  haveI : IsCyclic ↥(D₁ ⊔ D₂) := hcyc _ hCX hCp
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hD₁
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hD₂
  have hcard₁ : Nat.card (D₁.subgroupOf (D₁ ⊔ D₂)) = r ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, ha]
  have hcard₂ : Nat.card (D₂.subgroupOf (D₁ ⊔ D₂)) = r ^ b := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv, hb]
  rcases le_total a b with hab | hab
  · have h1 : D₁.subgroupOf (D₁ ⊔ D₂) ≤ D₂.subgroupOf (D₁ ⊔ D₂) :=
      (IsCyclic.subgroup_le_iff_card_dvd).2 (by rw [hcard₁, hcard₂]; exact pow_dvd_pow r hab)
    have h2 : D₁ ≤ D₂ := by
      have := Subgroup.map_mono (f := (D₁ ⊔ D₂).subtype) h1
      rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_left,
        Subgroup.map_subgroupOf_eq_of_le le_sup_right] at this
    exact false_of_sylow_le_of_commutator_eq_bot h₁ hc hd₁ P₁ (h2.trans hD₂K)
  · have h1 : D₂.subgroupOf (D₁ ⊔ D₂) ≤ D₁.subgroupOf (D₁ ⊔ D₂) :=
      (IsCyclic.subgroup_le_iff_card_dvd).2 (by rw [hcard₁, hcard₂]; exact pow_dvd_pow r hab)
    have h2 : D₂ ≤ D₁ := by
      have := Subgroup.map_mono (f := (D₁ ⊔ D₂).subtype) h1
      rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_left,
        Subgroup.map_subgroupOf_eq_of_le le_sup_right] at this
    exact false_of_sylow_le_of_commutator_eq_bot h₂ (by rw [Subgroup.commutator_comm]; exact hc)
      hd₂ P₂ (h2.trans hD₁K)

theorem map_pPrimeCore_le_of_isSubnormal {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    {Y : Subgroup X} (hY : Y.IsSubnormal) :
    (CFSG.pPrimeCore p Y).map Y.subtype ≤ CFSG.pPrimeCore p X := by
  have key : ∀ {Y Z : Subgroup X}, Y ≤ Z → Z ≤ Subgroup.normalizer (Y : Set X) →
      (CFSG.pPrimeCore p Y).map Y.subtype ≤ (CFSG.pPrimeCore p Z).map Z.subtype := by
    intro Y Z hYZ hZN
    have hLZ : (CFSG.pPrimeCore p Y).map Y.subtype ≤ Z := (Subgroup.map_subtype_le _).trans hYZ
    have hle : ((CFSG.pPrimeCore p Y).map Y.subtype).subgroupOf Z ≤ CFSG.pPrimeCore p Z := by
      apply le_sSup
      refine ⟨⟨fun l hl z => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using CFSG.Walter.conj_mem_map_of_characteristic (hZN z.2) hl
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv,
          Subgroup.card_map_of_injective Y.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
    calc (CFSG.pPrimeCore p Y).map Y.subtype
        = (((CFSG.pPrimeCore p Y).map Y.subtype).subgroupOf Z).map Z.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLZ).symm
      _ ≤ (CFSG.pPrimeCore p Z).map Z.subtype := Subgroup.map_mono hle
  induction hY with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => CFSG.Walter.conj_mem_map_of_characteristic ?_ hl⟩, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top g
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact CFSG.pPrimeCore_coprime_card
  | step Y Z hYZ hZ hN ih =>
    exact (key hYZ ((Subgroup.normal_subgroupOf_iff_le_normalizer hYZ).mp hN)).trans ih

theorem le_map_pPrimeCore_of_isSubnormal {r : ℕ} [Fact r.Prime] {K I N : Subgroup G} (hKI : K ≤ I)
    (hK : (K.subgroupOf I).IsSubnormal) (hIN : I ≤ N) (hIn : (I.subgroupOf N).Normal)
    (hcop : Nat.Coprime r (Nat.card K)) : K ≤ (CFSG.pPrimeCore r ↥N).map N.subtype := by
  have hKN : (K.subgroupOf N).IsSubnormal := by
    let ψ : (I.subgroupOf N) →* I :=
      { toFun := fun x => ⟨((x : N) : G), x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    have hK' : ((K.subgroupOf N).subgroupOf (I.subgroupOf N)).IsSubnormal := by
      convert hK.comap ψ using 1
      ext x
      exact Iff.rfl
    exact Subgroup.IsSubnormal.trans (fun x hx => hKI hx) hK' hIn.isSubnormal
  have h1 := map_pPrimeCore_le_of_isSubnormal r hKN
  have htop : CFSG.pPrimeCore r ↥(K.subgroupOf N) = ⊤ := by
    apply le_antisymm le_top
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKI.trans hIN)).toEquiv]
    exact hcop
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  intro x hx
  exact ⟨⟨x, hKI.trans hIN hx⟩, h1 hx, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6.N588
