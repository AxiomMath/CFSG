module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts3
public import CFSG.Quasithin.Vol2.Ch11SecGTSL2
public import CFSG.Quasithin.Background.KnownMultL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem le_center_of_normal {X : Type*} [Group X] (hq : CFSG.IsQuasisimple X) {N : Subgroup X}
    (hN : N.Normal) (hNt : N ≠ ⊤) : N ≤ Subgroup.center X := by
  obtain ⟨hperf, hs, -⟩ := hq
  have := hperf
  have := hs
  let π := QuotientGroup.mk' (Subgroup.center X)
  have hn : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with hb | ht
  · have h := (Subgroup.map_eq_bot_iff N).mp hb
    rwa [QuotientGroup.ker_mk'] at h
  · exfalso
    apply hNt
    have hsup : N ⊔ Subgroup.center X = ⊤ := by
      have h := Subgroup.comap_map_eq π N
      rw [ht, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      exact h.symm
    have hd : commutator X ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hd
    exact top_unique hd

theorem mem_center_of_comm_mem_center {X : Type*} [Group X] [Group.IsPerfect X] {w : X}
    (h : ∀ x : X, w * x * w⁻¹ * x⁻¹ ∈ Subgroup.center X) : w ∈ Subgroup.center X := by
  let f : X →* Subgroup.center X :=
    { toFun := fun x => ⟨w * x * w⁻¹ * x⁻¹, h x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := Subgroup.mem_center_iff.mp (h y) x
        simp only [Subgroup.coe_mul]
        calc w * (x * y) * w⁻¹ * (x * y)⁻¹ = w * x * w⁻¹ * x⁻¹ * (x * (w * y * w⁻¹ * y⁻¹) * x⁻¹) :=
              by group
          _ = w * x * w⁻¹ * x⁻¹ * (w * y * w⁻¹ * y⁻¹ * x * x⁻¹) := by rw [hc]
          _ = w * x * w⁻¹ * x⁻¹ * (w * y * w⁻¹ * y⁻¹) := by rw [mul_inv_cancel_right] }
  have hker : commutator X ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : f x = 1 := (MonoidHom.mem_ker).mp (hker Group.IsPerfect.mem_commutator)
  have h1 : w * x * w⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hx
  have h2 : w * x = x * w := by
    calc w * x = w * x * w⁻¹ * x⁻¹ * (x * w) := by group
      _ = x * w := by rw [h1, one_mul]
  exact h2.symm

variable {p : ℕ} [Fact p.Prime]

theorem wElt_sq_ne_one (hp2 : p ≠ 2) : (SecG.SL2.wElt : SL(2, ZMod p)) ^ 2 ≠ 1 := by
  have : Fact (2 < p) := ⟨lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)⟩
  intro h
  apply ZMod.neg_one_ne_one (n := p)
  have h00 := congrArg (fun A : SL(2, ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  simpa [SecG.SL2.coe_wElt, sq, Matrix.mul_apply, Fin.sum_univ_two] using h00

theorem exists_preimage {X : Type*} [Group X] {φ : X →* SL(2, ZMod p)}
    (hφ : Function.Surjective φ) :
    ∃ x : X, φ x = SecG.SL2.wElt ^ 2 ∧ ((Subgroup.center SL(2, ZMod p)).comap φ).Normal ∧
      (Subgroup.center SL(2, ZMod p)).comap φ ≠ ⊤ ∧
      x ∈ (Subgroup.center SL(2, ZMod p)).comap φ := by
  obtain ⟨x, hx⟩ := hφ (SecG.SL2.wElt ^ 2)
  obtain ⟨t, ht⟩ := hφ SecG.SL2.tElt
  refine ⟨x, hx, Subgroup.Normal.comap inferInstance φ, fun h => ?_, ?_⟩
  · have htN : t ∈ (Subgroup.center SL(2, ZMod p)).comap φ := by
      rw [h]
      exact Subgroup.mem_top t
    rw [Subgroup.mem_comap, ht] at htN
    exact SecG.SL2.tElt_not_mem_center htN
  · rw [Subgroup.mem_comap, hx]
    exact SecG.SL2.wElt_sq_mem_center

theorem false_of_simple {X : Type*} [Group X] [IsSimpleGroup X] (hp2 : p ≠ 2)
    {φ : X →* SL(2, ZMod p)} (hφ : Function.Surjective φ) : False := by
  obtain ⟨x, hx, hN, hNt, hxN⟩ := exists_preimage hφ
  rcases hN.eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.mem_bot] at hxN
    rw [hxN, map_one] at hx
    exact wElt_sq_ne_one hp2 hx.symm
  · exact hNt ht

theorem false_of_quasisimple {X : Type*} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hZ : Nat.card (Subgroup.center X) ∣ 3) (hp2 : p ≠ 2) {φ : X →* SL(2, ZMod p)}
    (hφ : Function.Surjective φ) : False := by
  obtain ⟨x, hx, hN, hNt, hxN⟩ := exists_preimage hφ
  have hxZ : x ∈ Subgroup.center X := le_center_of_normal hq hN hNt hxN
  have hx3 : x ^ 3 = 1 := by
    have h := (orderOf_dvd_natCard (⟨x, hxZ⟩ : Subgroup.center X)).trans hZ
    have h' := congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h)
    simpa using h'
  have hw2 := SecG.SL2.sq_eq_one_of_mem_center (SecG.SL2.wElt_sq_mem_center (k := ZMod p))
  have hz3 : ((SecG.SL2.wElt : SL(2, ZMod p)) ^ 2) ^ 3 = 1 := by
    rw [← hx, ← map_pow, hx3, map_one]
  apply wElt_sq_ne_one hp2
  set w := (SecG.SL2.wElt : SL(2, ZMod p))
  calc w ^ 2 = (w ^ 2) ^ 3 * ((w ^ 2) ^ 2)⁻¹ := by group
    _ = 1 := by rw [hz3, hw2, inv_one, one_mul]

end CFSG.Quasithin.Vol2.Ch11.O6

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem sl2pMultFact_holds : SL2pMultFact := by
  intro G _ _ K P Q p hp hp5 hperf hQP hPK hKP hKQ hPKQ ⟨φ, hφs, hφk⟩
  have : Fact p.Prime := ⟨hp⟩
  have hNQ : (Q.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQP.trans hPK)).mpr hKQ
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  have : Group.IsPerfect (↥K ⧸ Q.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hle : Q.subgroupOf K ≤ φ.ker := by
    intro x hx
    rw [hφk, Subgroup.mem_subgroupOf]
    exact hQP (Subgroup.mem_subgroupOf.mp hx)
  let φb : ↥K ⧸ Q.subgroupOf K →* SL(2, ZMod p) := QuotientGroup.lift _ φ hle
  have hφb : ∀ k : ↥K, φb (k : ↥K ⧸ Q.subgroupOf K) = φ k := fun k => QuotientGroup.lift_mk _ hle k
  have hφbs : Function.Surjective φb := fun y => by
    obtain ⟨x, rfl⟩ := hφs y
    exact ⟨x, hφb x⟩
  have hcen : φb.ker ≤ Subgroup.center (↥K ⧸ Q.subgroupOf K) := by
    intro z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    have hkP : (k : G) ∈ P := by
      rw [MonoidHom.mem_ker, hφb, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf] at hz
      exact hz
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective y
    have hc : ((k' * k : ↥K) : G)⁻¹ * ((k * k' : ↥K) : G) ∈ Q := by
      have := hPKQ (Subgroup.commutator_mem_commutator (P.inv_mem hkP) (K.inv_mem k'.2))
      rw [commutatorElement_def] at this
      simpa [mul_assoc] using this
    have heq : ((k' * k : ↥K) : ↥K ⧸ Q.subgroupOf K) = ((k * k' : ↥K) : ↥K ⧸ Q.subgroupOf K) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hc
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact heq
  set W := (Subgroup.center SL(2, ZMod p)).comap φb with hWdef
  have hWZ : W ≤ Subgroup.center (↥K ⧸ Q.subgroupOf K) := by
    intro w hw
    apply O6.mem_center_of_comm_mem_center
    intro x
    apply hcen
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hwc := Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp hw) (φb x)
    rw [← hwc]
    group
  have hWn : W.Normal := Subgroup.Normal.comap inferInstance φb
  let ψ := (QuotientGroup.mk' (Subgroup.center SL(2, ZMod p))).comp φb
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφbs
  have hker : ψ.ker = W := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hWdef, Subgroup.mem_comap]
  have hPSL : IsPSL 2 p 1 ((↥K ⧸ Q.subgroupOf K) ⧸ W) := by
    refine ⟨⟨hp, le_rfl, le_rfl, fun h => ?_, fun h => ?_⟩, ZMod p, inferInstance, inferInstance,
      by rw [Nat.card_zmod, pow_one], ⟨?_⟩⟩
    · simp only [pow_one, Prod.mk.injEq, true_and] at h
      omega
    · simp only [pow_one, Prod.mk.injEq, true_and] at h
      omega
    · exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod p))
  have hW2 := CFSG.Quasithin.l2MultiplierFact p hp hp5 _ inferInstance W hWZ hPSL
  have hbot : φb.ker = ⊥ := by
    by_contra hne
    obtain ⟨w₀, hw₀, -, -, hw₀W⟩ := O6.exists_preimage hφbs
    have hkW : φb.ker ≤ W := fun z hz => by
      rw [hWdef, Subgroup.mem_comap, (MonoidHom.mem_ker).mp hz]
      exact Subgroup.one_mem _
    have hlt : φb.ker < W := lt_of_le_of_ne hkW fun h => by
      have : w₀ ∈ φb.ker := by rw [h]; exact hw₀W
      rw [MonoidHom.mem_ker, hw₀] at this
      exact O6.wElt_sq_ne_one (by omega) this
    have h1 : 1 < Nat.card φb.ker := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have h2 := Subgroup.card_lt_of_lt hlt
    omega
  refine le_antisymm (fun g hg => ?_) hQP
  have h1 : ((⟨g, hPK hg⟩ : ↥K) : ↥K ⧸ Q.subgroupOf K) ∈ φb.ker := by
    rw [MonoidHom.mem_ker, hφb, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
    exact hg
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

end CFSG.Quasithin.Vol2.Ch11.SecD
