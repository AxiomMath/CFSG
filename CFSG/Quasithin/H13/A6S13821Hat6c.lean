module

public import CFSG.Quasithin.H13.A6S13821Hat6b
public import CFSG.Quasithin.H13.A6S13821zc
public import CFSG.Quasithin.H13.L32AC47e

public section

namespace CFSG.Quasithin.H13.A6.Hat6

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.Quasithin.H13.L32A.C.Alt6
open CFSG.Quasithin.E1.LiftS5 (quotConj quotConj_of_mem)

variable {G : Type} [Group G]

abbrev Kq (K : Subgroup G) : Type := ↥K ⧸ CFSG.pCore 2 ↥K

@[expose] noncomputable def piOf {K : Subgroup G}
    (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6) : ↥K →* A6 :=
  φ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center (Kq K))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))

theorem piOf_apply {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6) (k : ↥K) :
    piOf φ k = φ (QuotientGroup.mk (QuotientGroup.mk k : Kq K)) := rfl

theorem piOf_surjective {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6) :
    Function.Surjective (piOf φ) :=
  φ.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))

theorem piOf_eq_one_iff {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6) (k : ↥K) :
    piOf φ k = 1 ↔ (k : G) ∈ oTwoZIn K := by
  rw [piOf_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨k, h, rfl⟩
  · rintro ⟨k', hk', hkk⟩
    rwa [← Subtype.ext hkk]

@[expose] noncomputable def sigOf {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut A6 :=
  (MulAut.congr φ).toMonoidHom.comp ((centerQuotientHom (Kq K)).comp (quotConj K))

theorem sigOf_piOf {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6)
    (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    sigOf φ g (piOf φ k) = piOf φ ⟨(g : G) * k * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp g.2 k).mp k.2⟩ := by
  show φ (centerQuotientHom (Kq K) (quotConj K g)
    (φ.symm (φ (QuotientGroup.mk (QuotientGroup.mk k : Kq K))))) = _
  rw [MulEquiv.symm_apply_apply, piOf_apply]
  congr 1

theorem sigOf_of_mem {K : Subgroup G} (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6)
    (g : ↥(Subgroup.normalizer (K : Set G))) (hg : (g : G) ∈ K) :
    sigOf φ g = MulAut.conj (piOf φ ⟨g, hg⟩) := by
  ext x
  obtain ⟨k, rfl⟩ := piOf_surjective φ x
  rw [sigOf_piOf, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem exists_inner_sigOf {K : Subgroup G} [Finite G] [Group.IsPerfect (Kq K)]
    (hZ : Nat.card (Subgroup.center (Kq K)) = 3) (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6)
    {g : ↥(Subgroup.normalizer (K : Set G))} (hg2 : g * g = 1)
    (hgZ : ∀ c ∈ Subgroup.center (Kq K), quotConj K g c = c) :
    ∃ a : A6, sigOf φ g = MulAut.conj a := by
  have h2 : quotConj K g * quotConj K g = 1 := by rw [← map_mul, hg2, map_one]
  obtain ⟨a, ha⟩ := exists_inner_of_invol hZ φ (quotConj K g) h2 hgZ
  refine ⟨a, MulEquiv.ext fun x => ?_⟩
  obtain ⟨q, rfl⟩ := φ.surjective x
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  show φ (centerQuotientHom (Kq K) (quotConj K g) (φ.symm (φ (QuotientGroup.mk q)))) = _
  rw [MulEquiv.symm_apply_apply, MulAut.conj_apply]
  rw [← ha q]
  exact congrArg φ (onCenterQuotient_apply_mk (quotConj K g) q)

end CFSG.Quasithin.H13.A6.Hat6

namespace CFSG.Quasithin.H13.A6.Setting4

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.Quasithin.H13.L32A.C.Alt6
  CFSG.Quasithin.H13.A6.Hat6
open CFSG.Quasithin.E1.LiftS5 (quotConj quotConj_of_mem)

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_QH_of_sigOf_eq_one (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ (S.L1 ⊔ T))
    (hK : K ∈ cComp H) [Group.IsPerfect (Kq K)]
    (φ : Kq K ⧸ Subgroup.center (Kq K) ≃* A6) {r : G} (hrR : r ∈ pCoreOf 2 (S.L1 ⊔ T))
    (hr : sigOf φ ⟨r, hKn (((pCoreOf_le 2 _).trans hH.1.1) hrR)⟩ = 1) :
    r ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hLTH : S.L1 ⊔ T ≤ H := hF.L₁T_le_H
  set R := pCoreOf 2 (S.L1 ⊔ T) with hR
  have hQR : pCoreOf 2 H ≤ R :=
    le_pCoreOf_of_le_normalizer 2 ((F7.isSylowTwoOf_pCoreOf_le hF.sylow_H).trans le_sup_right)
      (hLTH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  set C : Subgroup G := ((quotConj K).ker).map (Subgroup.normalizer (K : Set G)).subtype with hC
  have hmemC : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)),
      g ∈ C ↔ quotConj K ⟨g, hg⟩ = 1 := by
    intro g hg
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact hg'
    · intro h
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hCN : C ≤ Subgroup.normalizer (K : Set G) := Subgroup.map_subtype_le _
  have hcomm : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)), g ∈ C →
      ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    intro g hg hgC k hk
    have h1 := congrArg (fun α : MulAut (Kq K) => α (QuotientGroup.mk ⟨k, hk⟩))
      ((hmemC hg).mp hgC)
    simp only [MulAut.one_apply] at h1
    rw [A6L24.quotConj_mk, QuotientGroup.eq_iff_div_mem, A6L24.mem_pCore_iff'] at h1
    simpa [div_eq_mul_inv] using h1
  have hrH : r ∈ H := ((pCoreOf_le 2 _).trans hLTH) hrR
  have hrC : r ∈ C := by
    rw [hmemC (hKn hrH)]
    apply centerQuotientHom_injective (Kq K)
    rw [map_one]
    apply (MulAut.congr φ).injective
    rw [map_one]
    exact hr
  set N : Subgroup G := R ⊓ C with hN
  have hNH : N ≤ H := inf_le_left.trans ((pCoreOf_le 2 _).trans hLTH)
  have hN2 : IsPGroup 2 N := (pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hCn : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro g hg x hx
    have hxN := hCN hx
    rw [hmemC (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxN) (Subgroup.inv_mem _ hg))]
    have h1 : quotConj K ⟨g * x * g⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxN)
        (Subgroup.inv_mem _ hg)⟩ = quotConj K ⟨g, hg⟩ * quotConj K ⟨x, hxN⟩ *
          (quotConj K ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1, (hmemC hxN).mp hx, mul_one, mul_inv_cancel]
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    have hkey : ∀ g ∈ H, (∀ x ∈ N, g * x * g⁻¹ ∈ N) → (∀ x ∈ N, g⁻¹ * x * g⁻¹⁻¹ ∈ N) →
        g ∈ Subgroup.normalizer (N : Set G) := by
      intro g hg h1 h2
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => h1 x hx, fun hx => ?_⟩
      have h3 := h2 _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h3
    have hLT : S.L1 ⊔ T ≤ Subgroup.normalizer (N : Set G) := by
      intro g hg
      have hgH := hLTH hg
      refine hkey g hgH (fun x hx => ⟨?_, hCn g (hKn hgH) x hx.2⟩) (fun x hx => ⟨?_, ?_⟩)
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hg) x).mp hx.1
      · have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _
          ((S.L1 ⊔ T).inv_mem hg)) x).mp hx.1
        simpa using this
      · simpa using hCn g⁻¹ (Subgroup.inv_mem _ (hKn hgH)) x hx.2
    have hKN' : K ≤ Subgroup.normalizer (N : Set G) := by
      intro k hk
      have hkH := hKH hk
      have hconj : ∀ k ∈ K, ∀ x ∈ N, k * x * k⁻¹ ∈ N := by
        intro k hk x hx
        have hxN := hCN hx.2
        refine ⟨?_, hCn k (hKn (hKH hk)) x hx.2⟩
        have h1 := hcomm hxN hx.2 k hk
        have h2 : (x * k * x⁻¹ * k⁻¹)⁻¹ * x ∈ R :=
          R.mul_mem (R.inv_mem (hQR (hOQ h1))) hx.1
        have e : k * x * k⁻¹ = (x * k * x⁻¹ * k⁻¹)⁻¹ * x := by group
        rw [e]
        exact h2
      exact hkey k hkH (hconj k hk) (fun x hx => by
        simpa using hconj k⁻¹ (K.inv_mem hk) x hx)
    rw [hHK]
    exact sup_le hKN' hLT
  have hNQ : N ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer 2 hNH hHN hN2
  exact hNQ ⟨hrR, hrC⟩

end CFSG.Quasithin.H13.A6.Setting4
