module

public import CFSG.Quasithin.Background.C124AsmOrder
public import CFSG.Quasithin.Background.C124AsmQuot
public import CFSG.Quasithin.Background.C124Perf
public import CFSG.Quasithin.Background.F1Models

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecA

variable {G : Type} [Group G] [Finite G]

theorem alt_noncomm {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) :
    ∃ a b : ↥(alternatingGroup (Fin m)), a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin m)) := isSimpleGroup_alt (by omega)
  have : IsMulCommutative ↥(alternatingGroup (Fin m)) := ⟨⟨fun a b => h a b⟩⟩
  have hp := hs.prime_card
  rcases card_alt_cases hm with ⟨-, h5⟩ | ⟨-, h5⟩ | ⟨-, h5⟩ <;> rw [h5] at hp <;> norm_num at hp

omit [Finite G] in
theorem pCore_le_subgroupOf_oTwoZIn' (L : Subgroup G) :
    CFSG.pCore 2 ↥L ≤ (oTwoZIn L).subgroupOf L := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  refine ⟨x, ?_, rfl⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
  exact Subgroup.one_mem _

theorem isQuasisimple_of_altQuotient {X L : Subgroup G} {m : ℕ} (hL : L ∈ cComp X)
    (halt : IsAltQuotient L (oTwoZIn L) m) (hm : m = 5 ∨ m = 6 ∨ m = 7) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨φ, hφs, hφk⟩ := halt
  have hle : CFSG.pCore 2 ↥L ≤ φ.ker := hφk ▸ pCore_le_subgroupOf_oTwoZIn' L
  let φ' : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(alternatingGroup (Fin m)) := QuotientGroup.lift _ φ hle
  have hφ's : Function.Surjective φ' := fun a => by
    obtain ⟨x, rfl⟩ := hφs a
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker : φ'.ker = Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker]
    have h1 : φ' (QuotientGroup.mk x) = φ x := rfl
    rw [h1, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
    unfold oTwoZIn preimageModTwoCore
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      subst this
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin m)) := isSimpleGroup_alt (by omega)
  let e : ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ≃*
      ↥(alternatingGroup (Fin m)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's)
  have : Group.IsPerfect ↥L := isPerfect_of_comm_eq (perfect_of_mem_cComp hL)
  refine ⟨Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _), e.isSimpleGroup, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, hab⟩ := alt_noncomm hm
  exact hab (e.symm.injective (by rw [map_mul, map_mul]; exact hcon _ _))

theorem exists_surj_alt_aux {X V L : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
    (hred : IsTwoReducedIn X V) (hLX : L ≤ X) (hn : X ≤ Subgroup.normalizer (L : Set G))
    (halt : IsAltQuotient L (oTwoZIn L) m) (hq : CFSG.IsQuasisimple ↥(autI hV L)) (hm : 5 ≤ m) :
    ∃ ψ : ↥(autI hV L) →* ↥(alternatingGroup (Fin m)), Function.Surjective ψ := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hLX.trans hred.2.1
  have hLC : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)).trans
      (pCoreOf_le_centralizer hred)
  obtain ⟨φ, hφs, hφk⟩ := halt
  set σ := starHom hV L hLN with hσ
  have hσs : Function.Surjective σ := starHom_surjective hV hLN
  have hσk : ∀ x : ↥L, x ∈ σ.ker ↔ (x : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
    intro x
    rw [ker_starHom hV hLN, Subgroup.mem_subgroupOf]
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin m)) := isSimpleGroup_alt hm
  have hK : σ.ker ≤ φ.ker := by
    have hnorm : (σ.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφs
    rcases hsimple.eq_bot_or_eq_top_of_normal (σ.ker.map φ) with h | h
    · intro k hk
      have : φ k ∈ σ.ker.map φ := ⟨k, hk, rfl⟩
      rw [h] at this
      exact this
    · exfalso
      refine not_commute_of_isQuasisimple hq ?_
      have hrep : ∀ a : ↥(autI hV L), ∃ n : ↥L, (n : G) ∈ oTwoZIn L ∧ σ n = a := by
        intro a
        obtain ⟨l, rfl⟩ := hσs a
        have : φ l ∈ σ.ker.map φ := by rw [h]; trivial
        obtain ⟨k, hk, hkl⟩ := this
        refine ⟨k⁻¹ * l, ?_, ?_⟩
        · have h1 : k⁻¹ * l ∈ φ.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hkl, inv_mul_cancel]
          rw [hφk, Subgroup.mem_subgroupOf] at h1
          exact h1
        · rw [map_mul, map_inv, (MonoidHom.mem_ker.1 hk), inv_one, one_mul]
      intro a b
      obtain ⟨n, hn, rfl⟩ := hrep a
      obtain ⟨w, rfl⟩ := hσs b
      have hc := commutator_mem_pCoreOf_of_mem_oTwoZIn hn w
      have hcC : ((n * w * n⁻¹ * w⁻¹ : ↥L) : G) ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
        ⟨(n * w * n⁻¹ * w⁻¹ : ↥L).2, hLC hc⟩
      have h1 : σ (n * w * n⁻¹ * w⁻¹) = 1 := (hσk _).2 hcC
      have h2 : σ n * σ w * (σ n)⁻¹ * (σ w)⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using h1
      calc σ n * σ w = (σ n * σ w * (σ n)⁻¹ * (σ w)⁻¹) * (σ w * σ n) := by group
        _ = σ w * σ n := by rw [h2, one_mul]
  let e : ↥L ⧸ σ.ker ≃* ↥(autI hV L) := QuotientGroup.quotientKerEquivOfSurjective σ hσs
  refine ⟨(QuotientGroup.lift σ.ker φ hK).comp e.symm.toMonoidHom, fun a => ?_⟩
  obtain ⟨l, rfl⟩ := hφs a
  refine ⟨σ l, ?_⟩
  have : e.symm (σ l) = QuotientGroup.mk l := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp [this]

theorem card_of_surj_alt {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {m : ℕ}
    (hq : CFSG.IsQuasisimple ↥H) (ho2 : pCoreOf 2 H = ⊥) (hm : 5 ≤ m)
    (hψ : ∃ ψ : ↥H →* ↥(alternatingGroup (Fin m)), Function.Surjective ψ) :
    ∃ z : ℕ, Odd z ∧ Nat.card ↥H = Nat.card ↥(alternatingGroup (Fin m)) * z := by
  obtain ⟨ψ, hψs⟩ := hψ
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin m)) := isSimpleGroup_alt hm
  have hKne : ψ.ker ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(alternatingGroup (Fin m)))
    obtain ⟨g, rfl⟩ := hψs x
    exact hx (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g))
  have hKc : ψ.ker ≤ Subgroup.center ↥H :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
      (B1Red.isQuasisimple_to_open hq) ψ.ker hKne
  refine ⟨Nat.card ψ.ker, ?_, ?_⟩
  · by_contra hodd
    have h2 : 2 ∣ Nat.card ψ.ker := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.ker) 2 h2
    set w' : MulAut W := (((w : ↥ψ.ker) : ↥H) : MulAut W) with hw'
    have hw2 : w' ^ 2 = 1 := by
      have : (w : ↥ψ.ker) ^ 2 = 1 := hw ▸ pow_orderOf_eq_one w
      have h3 := congrArg (fun x : ↥ψ.ker => (((x : ↥H) : MulAut W))) this
      simpa using h3
    have hwH : w' ∈ H := ((w : ↥ψ.ker) : ↥H).2
    have hcent : ∀ g ∈ H, Commute g w' := fun g hg => by
      have := Subgroup.mem_center_iff.1 (hKc w.2) ⟨g, hg⟩
      exact congrArg Subtype.val this
    have hcentz : H ≤ Subgroup.centralizer (Subgroup.zpowers w' : Set (MulAut W)) := fun g hg =>
      Subgroup.mem_centralizer_iff.2 fun h hh => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        exact (((hcent g hg).symm).zpow_left k).eq
    have hp : IsPGroup 2 (Subgroup.zpowers w') := by
      rintro ⟨x, hx⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine ⟨1, Subtype.ext ?_⟩
      show (w' ^ k) ^ 2 ^ 1 = 1
      rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw2, one_zpow]
    have hN : Subgroup.zpowers w' ≤ pCoreOf 2 H :=
      le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.2 hwH)
        (hcentz.trans (Subgroup.centralizer_le_normalizer _)) hp
    rw [ho2] at hN
    have h1 : w' = 1 := Subgroup.mem_bot.1 (hN (Subgroup.mem_zpowers w'))
    have h4 : w = 1 := Subtype.ext (Subtype.ext h1)
    rw [h4, orderOf_one] at hw
    omega
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv]

end CFSG.Quasithin.C124
