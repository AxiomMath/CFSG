module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1c
public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzHeCore

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem kzPCoreOfLe_kz3 {G : Type} [Group G] (H : Subgroup G) : CFSG.Open.pCoreOf 2 H ≤ H := by
  intro n hn
  obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hn
  exact w.2

theorem kzPCoreOfConj_kz3 {G : Type} [Group G] {Gz : Subgroup G} {g n : G} (hg : g ∈ Gz)
    (hn : n ∈ pCoreOf 2 Gz) : g * n * g⁻¹ ∈ pCoreOf 2 Gz := by
  have hpG : CFSG.Open.pCoreOf 2 Gz ≤ Gz := kzPCoreOfLe_kz3 Gz
  have hnG : n ∈ Gz := hpG hn
  have hmem : (⟨n, hnG⟩ : ↥Gz) ∈ CFSG.pCore 2 ↥Gz :=
    (CFSG.Quasithin.P134.mem_pCoreOf_iff hnG).mp hn
  have hc := Subgroup.Normal.conj_mem (CFSG.pCore_normal (p := 2) (G := ↥Gz)) _ hmem ⟨g, hg⟩
  have hgG : g * n * g⁻¹ ∈ Gz := Gz.mul_mem (Gz.mul_mem hg hnG) (Gz.inv_mem hg)
  have heq : (⟨g * n * g⁻¹, hgG⟩ : ↥Gz) = ⟨g, hg⟩ * ⟨n, hnG⟩ * ⟨g, hg⟩⁻¹ := by
    apply Subtype.ext
    simp [mul_assoc]
  refine (CFSG.Quasithin.P134.mem_pCoreOf_iff hgG).mpr ?_
  rw [heq]
  exact hc

theorem kzCase0Comm_kz3 {G : Type} [Group G] [Finite G] {Gz X K0 : Subgroup G}
    (hXGz : X ≤ Gz) (hX0 : Gz ≤ Subgroup.normalizer (X : Set G)) (hK0G : K0 ≤ Gz)
    (hK0perf : ⁅K0, K0⁆ = K0) (hAut : KzAutE9Perfect_kz3)
    (hrel : (CFSG.Open.pCoreOf 2 X).relIndex X = 9)
    (hXexp : ∀ x ∈ X, x ^ 3 ∈ CFSG.Open.pCoreOf 2 X) :
    ∀ p ∈ X, ∀ k ∈ K0, p * k * p⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Gz := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOX : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 Gz :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((kzPCoreOfLe_kz3 X).trans hXGz)
      (fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X (hX0 hg))
      (kzIsPGroupPCoreOf_kz3 X)
  have hsub : (CFSG.Open.pCoreOf 2 X).subgroupOf X = CFSG.pCore 2 ↥X := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      have hwz' : w = z := Subtype.ext hwz
      rw [← hwz']
      exact hw
    · intro hz
      exact Subgroup.mem_map_of_mem _ hz
  have hcardA : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = 9 := by
    rw [Subgroup.relIndex, hsub] at hrel
    exact hrel
  have hAexp : ∀ a : ↥X ⧸ CFSG.pCore 2 ↥X, a ^ 3 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have h1 := (CFSG.Quasithin.P134.mem_pCoreOf_iff (X.pow_mem x.2 3)).mp (hXexp x x.2)
      have h2 : x ^ 3 = ⟨(x : G) ^ 3, X.pow_mem x.2 3⟩ := Subtype.ext (by simp)
      rw [h2]
      exact h1
  have hk0 : ∀ k : ↥K0, (k : G) ∈ Subgroup.normalizer (X : Set G) := fun k => hX0 (hK0G k.2)
  let aut : ↥K0 → MulAut (↥X ⧸ CFSG.pCore 2 ↥X) := fun k =>
    MulEquiv.ofBijective (CFSG.Quasithin.H13.kzQmap_kz2 X (k : G) (hk0 k))
      (CFSG.Quasithin.H13.kzQmap_bijective_kz2 (hk0 k))
  let θ : ↥K0 →* MulAut (↥X ⧸ CFSG.pCore 2 ↥X) :=
    MonoidHom.mk' aut (fun a b => by
      ext q
      exact CFSG.Quasithin.H13.kzQmap_mul_kz2 (hk0 a) (hk0 b) (hk0 (a * b)) q)
  have hθ : ∀ k : ↥K0, θ k = 1 := fun k =>
    kzHomTrivialOfPerfect_kz3 θ (kzTopCommutatorOfPerfect_kz3 hK0perf)
      (hAut (↥X ⧸ CFSG.pCore 2 ↥X) hcardA hAexp) k
  intro p hp k hk
  set x : ↥X := ⟨p, hp⟩ with hx
  have hθk : aut ⟨k, hk⟩ = 1 := hθ ⟨k, hk⟩
  have hq : CFSG.Quasithin.H13.kzQmap_kz2 X k (hk0 ⟨k, hk⟩) (QuotientGroup.mk x) =
      QuotientGroup.mk x := by
    have := congrArg (fun f : MulAut (↥X ⧸ CFSG.pCore 2 ↥X) => f (QuotientGroup.mk x)) hθk
    simpa [aut] using this
  rw [CFSG.Quasithin.H13.kzQmap_mk_kz2] at hq
  have hN1 := (QuotientGroup.eq).mp hq
  set y : ↥X := x * ((CFSG.Quasithin.H13.kzConjK_kz2 X k (hk0 ⟨k, hk⟩) x)⁻¹ * x) * x⁻¹ with hy
  have hyN : y ∈ CFSG.pCore 2 ↥X :=
    Subgroup.Normal.conj_mem (CFSG.pCore_normal (p := 2) (G := ↥X)) _ hN1 x
  have hval : (y : G) = p * k * p⁻¹ * k⁻¹ := by
    rw [hy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
    rw [CFSG.Quasithin.H13.kzConjK_val_kz2]
    group
  have hmemO : (y : G) ∈ CFSG.Open.pCoreOf 2 X := (CFSG.Quasithin.P134.mem_pCoreOf_iff y.2).mpr hyN
  rw [← hval]
  exact hOX hmemO

theorem kzConjComm_kz3 {G : Type} [Group G] [Finite G] {Gz K0 L' T X : Subgroup G}
    (hA37 : CFSG.Quasithin.A37Statement (↥Gz ⧸ CFSG.pCore 2 ↥Gz))
    (hL' : L' ∈ CFSG.Quasithin.cComp Gz) (hK0 : K0 ∈ CFSG.Quasithin.cComp Gz) (hLK : L' ≠ K0)
    (hTGz : T ≤ Gz) (hTN : T ≤ Subgroup.normalizer (K0 : Set G))
    (hXL : X ≤ CFSG.Quasithin.conjClosure L' T) :
    ∀ x ∈ X, ∀ k ∈ K0, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Gz := by
  classical
  let C : Subgroup G :=
    { carrier := {x | x ∈ Gz ∧ ∀ k ∈ K0, x * k * x⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Gz}
      mul_mem' := by
        rintro a b ⟨ha, hak⟩ ⟨hb, hbk⟩
        refine ⟨Gz.mul_mem ha hb, fun k hk => ?_⟩
        have e : a * b * k * (a * b)⁻¹ * k⁻¹ =
            a * (b * k * b⁻¹ * k⁻¹) * a⁻¹ * (a * k * a⁻¹ * k⁻¹) := by group
        rw [e]
        exact (CFSG.Open.pCoreOf 2 Gz).mul_mem (kzPCoreOfConj_kz3 ha (hbk k hk)) (hak k hk)
      one_mem' := ⟨Gz.one_mem, fun k _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, hak⟩
        refine ⟨Gz.inv_mem ha, fun k hk => ?_⟩
        have e : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ = a⁻¹ * (a * k * a⁻¹ * k⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact kzPCoreOfConj_kz3 (Gz.inv_mem ha) ((CFSG.Open.pCoreOf 2 Gz).inv_mem (hak k hk)) }
  have hCge : CFSG.Quasithin.conjClosure L' T ≤ C := by
    apply CFSG.Quasithin.conjClosure_le
    intro t ht z hz
    have htG : t ∈ Gz := hTGz ht
    have hzG : z ∈ Gz := le_of_mem_cComp hL' hz
    have hLt := CFSG.Quasithin.map_conj_mem_cComp hL' htG
    have hLe : L'.map (MulEquiv.toMonoidHom (MulAut.conj t)) ≠ K0 := by
      intro hEq
      apply hLK
      ext y
      have hy : ∀ w, w ∈ L' ↔ t * w * t⁻¹ ∈ K0 := by
        intro w
        constructor
        · intro hw
          rw [← hEq]
          exact Subgroup.mem_map_of_mem _ hw
        · intro hw
          rw [← hEq] at hw
          obtain ⟨w', hw', hww'⟩ := Subgroup.mem_map.mp hw
          have hw'eq : w' = w := by
            simpa using hww'
          rw [← hw'eq]
          exact hw'
      rw [hy y]
      exact (Subgroup.mem_normalizer_iff.mp (hTN ht) y).symm
    have hxL : t * z * t⁻¹ ∈ L'.map (MulEquiv.toMonoidHom (MulAut.conj t)) :=
      Subgroup.mem_map_of_mem _ hz
    refine ⟨Gz.mul_mem (Gz.mul_mem htG hzG) (Gz.inv_mem htG), fun k hk => ?_⟩
    have hcomm := CFSG.Quasithin.commutator_le_pCoreOf_of_ne hA37 hLt hK0 hLe
    exact hcomm (Subgroup.commutator_mem_commutator hxL hk)
  intro x hx k hk
  exact ((hCge (hXL hx)).2 k hk)

end CFSG.Quasithin.H13
