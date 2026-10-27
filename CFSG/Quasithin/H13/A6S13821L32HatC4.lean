module

public import CFSG.Quasithin.H13.A6S13821L32HatC3

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace L32HatC4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

abbrev NV (T V : Subgroup G) : Subgroup G := Subgroup.normalizer ((fsuV1 T V : Subgroup G) : Set G)

abbrev QV (T V : Subgroup G) : Type _ := SecQuot (NV T V) (fsuV1 T V)

abbrev UT (T V : Subgroup G) (Vp H : Subgroup G) : Subgroup (QV T V) :=
  tildeOf (fsuV1 T V) (conjClosure Vp H)

abbrev sm (T V : Subgroup G) {x : G} (hx : x ∈ NV T V) : QV T V :=
  secMk (NV T V) (fsuV1 T V) ⟨x, hx⟩

noncomputable def actU {Vp H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) Vp H) :
    H →* MulAut ↥(UT T V Vp H) := by
  refine (conjAct (UT T V Vp H)).comp
    { toFun := fun h => ⟨sm T V (hF.H_normalizes_V₁ h.2), ?_⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext
        (map_mul (secMk (NV T V) (fsuV1 T V)) ⟨(a : G), hF.H_normalizes_V₁ a.2⟩
          ⟨(b : G), hF.H_normalizes_V₁ b.2⟩) }
  exact HypF91.tilde_le_normalizer (B := H) (V₁ := fsuV1 T V) (Vp := Vp) (H := H) (le_refl H)
    (secMk_mem_secImg (A := NV T V) (B := fsuV1 T V) (x := ⟨(h : G), hF.H_normalizes_V₁ h.2⟩) h.2)

theorem coe_actU {Vp H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) Vp H) (h : H)
    (x : ↥(UT T V Vp H)) :
    ((actU hF h x : ↥(UT T V Vp H)) : QV T V) =
      sm T V (hF.H_normalizes_V₁ h.2) * (x : QV T V) * (sm T V (hF.H_normalizes_V₁ h.2))⁻¹ :=
  AutOn.coe_conjAct_apply _ _ _

theorem sm_comm_UT {Vp H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) Vp H) {q : G}
    (hq : q ∈ pCoreOf 2 H) (hqN : q ∈ NV T V) :
    ∀ x ∈ UT T V Vp H, sm T V hqN * x = x * sm T V hqN := by
  have hmem : sm T V hqN ∈ tildeOf (fsuV1 T V) H ⊓
      Subgroup.centralizer ((UT T V Vp H : Subgroup (QV T V)) : Set (QV T V)) := by
    rw [HypF91.tilde_inf_centralizer_pCoreOf hF (le_refl H)]
    exact secMk_mem_secImg (A := NV T V) (B := fsuV1 T V) (x := ⟨q, hqN⟩)
      ⟨pCoreOf_le 2 H hq, hq⟩
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp hmem.2 x hx).symm

theorem actU_eq_one_of_pCore {Vp H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) Vp H) {q : G}
    (hq : q ∈ pCoreOf 2 H) (qH : q ∈ H) : actU hF ⟨q, qH⟩ = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [coe_actU]
  have hc := sm_comm_UT hF hq (hF.H_normalizes_V₁ qH) x x.2
  rw [hc, mul_inv_cancel_right]
  rfl

theorem fsuV1_le_pCore {Vp H : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) Vp H)
    (hV1H : fsuV1 T V ≤ H) : fsuV1 T V ≤ pCoreOf 2 H := by
  refine L32HatC3.le_pCoreOf_of_two hV1H (hF.H_normalizes_V₁) fun y hy => ⟨1, ?_⟩
  have hcard := hF.card_V₁
  have hord : orderOf (⟨y, hy⟩ : ↥(fsuV1 T V)) ∣ 2 := by
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have h2 : (⟨y, hy⟩ : ↥(fsuV1 T V)) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  simpa using congrArg Subtype.val h2

theorem actU_ne_one_of_not_pCore {Vp H K : Subgroup G} (hF : HypF91 T V L (fsuV1 T V) Vp H)
    (hKH : K ≤ H) (hV1H : fsuV1 T V ≤ H) {k : G} (hk : k ∈ K) (hkQ : k ∉ pCoreOf 2 H) :
    actU hF ⟨k, hKH hk⟩ ≠ 1 := by
  intro h1
  have hkN := hF.H_normalizes_V₁ (hKH hk)
  have hcent : sm T V hkN ∈
      Subgroup.centralizer ((UT T V Vp H : Subgroup (QV T V)) : Set (QV T V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : actU hF ⟨k, hKH hk⟩ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [h1]; rfl
    have hco := congrArg (fun y : ↥(UT T V Vp H) => (y : QV T V)) hx'
    simp only at hco
    rw [coe_actU] at hco
    exact (mul_inv_eq_iff_eq_mul.mp hco).symm
  have h0 : sm T V hkN ∈ tildeOf (fsuV1 T V) K ⊓
      Subgroup.centralizer ((UT T V Vp H : Subgroup (QV T V)) : Set (QV T V)) :=
    ⟨secMk_mem_secImg (A := NV T V) (B := fsuV1 T V) (x := ⟨k, hkN⟩) hk, hcent⟩
  rw [HypF91.tilde_inf_centralizer_pCoreOf hF hKH] at h0
  obtain ⟨y, hy, hyk⟩ := mem_secImg.mp h0
  have hv : (y : G)⁻¹ * k ∈ fsuV1 T V := by
    have h' := secMk_eq_secMk_iff.mp hyk
    exact h'
  apply hkQ
  have hkeq : k = (y : G) * ((y : G)⁻¹ * k) := by group
  rw [hkeq]
  exact (pCoreOf 2 H).mul_mem (Subgroup.mem_inf.mp hy).2 (fsuV1_le_pCore hF hV1H hv)

theorem actU_comm_X {S : Setting4 G T L V} {H K : Subgroup G}
    (hF : HypF91 T V L (fsuV1 T V) S.V3 H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hKH : K ≤ H) (hXH : S.X13820 ≤ H)
    (hX : ∀ x ∈ S.X13820, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K)
    {x k : G} (hx : x ∈ S.X13820) (hk : k ∈ K) :
    actU hF ⟨x, hXH hx⟩ * actU hF ⟨k, hKH hk⟩ = actU hF ⟨k, hKH hk⟩ * actU hF ⟨x, hXH hx⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : pCoreOf 2 K ≤ pCoreOf 2 H :=
    L32HatC3.le_pCoreOf_of_two ((pCoreOf_le 2 K).trans hKH)
      (hKn.trans (normalizer_le_normalizer_pCoreOf 2 K))
      (fun y hy => L32HatC3.two_pow_of_mem_pCoreOf hy)
  have hqQ : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H := hK2 (hX x hx k hk)
  have hqH : x * k * x⁻¹ * k⁻¹ ∈ H := pCoreOf_le 2 H hqQ
  have hxkH : x * k ∈ H := H.mul_mem (hXH hx) (hKH hk)
  have e : (⟨x * k, hxkH⟩ : ↥H) = ⟨x * k * x⁻¹ * k⁻¹, hqH⟩ * ⟨k, hKH hk⟩ * ⟨x, hXH hx⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  have h1 : actU hF ⟨x * k, hxkH⟩ = actU hF ⟨k, hKH hk⟩ * actU hF ⟨x, hXH hx⟩ := by
    rw [e, map_mul, map_mul, actU_eq_one_of_pCore hF hqQ hqH, one_mul]
  have h2 : actU hF ⟨x * k, hxkH⟩ = actU hF ⟨x, hXH hx⟩ * actU hF ⟨k, hKH hk⟩ := by
    rw [← map_mul]
    rfl
  exact h2.symm.trans h1

theorem exists_rhoPi {K : Subgroup G} {Z : Type*} [Group Z] (π : ↥K →* SL3.S)
    (hπ : Function.Surjective π) (σ : ↥K →* Z) (hσ : ∀ k : ↥K, π k = 1 → σ k = 1) :
    ∃ ρ : SL3.S →* Z, ∀ k : ↥K, ρ (π k) = σ k := by
  refine ⟨(QuotientGroup.lift π.ker σ (fun k hk => MonoidHom.mem_ker.mpr
      (hσ k (MonoidHom.mem_ker.mp hk)))).comp
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom, fun k => ?_⟩
  have e : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π k) =
      (k : ↥K ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, QuotientGroup.lift_mk]

theorem H_le_normalizer_X {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz)
    (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) (hHK : H = K ⊔ (S.L1 ⊔ T)) :
    H ≤ Subgroup.normalizer (S.X13820 : Set G) := by
  have hne := L32HatStep.oTwoRes_solvRad_ne_bot_hat h139 h37 h38 h1334 hS hhat hH hK hKn hP hHK
  have hXeq : oTwoRes (solvRad H) = S.X13820 := by
    rcases S.oTwoRes_solvRad_cases h139 h1334 h13 hS hH with h | ⟨hnh, -⟩ | ⟨-, h⟩
    · exact absurd h hne
    · exact absurd hhat hnh
    · rw [h, S.X13820_of_hat hhat]
  rw [← hXeq]
  exact A5.le_normalizer_oTwoRes_of_le_normalizer
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H))

theorem card_tilde_V3 {Vp : Subgroup G} (hV1 : fsuV1 T V ≤ Vp) (hVN : Vp ≤ NV T V)
    (hc1 : Nat.card (fsuV1 T V) = 2) (hc3 : Nat.card Vp = 8) :
    Nat.card ↥(tildeOf (fsuV1 T V) Vp) = 4 := by
  have hbot : secImg (NV T V) (fsuV1 T V) (fsuV1 T V) = ⊥ := by
    ext y
    rw [mem_secImg, Subgroup.mem_bot]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact secMk_eq_one_iff.mpr hx
    · rintro rfl
      exact ⟨1, (fsuV1 T V).one_mem, map_one _⟩
  have hrel := relIndex_secImg_of_inf_le (A := NV T V) (K := fsuV1 T V) (C := fsuV1 T V)
    (X := Vp) hV1 hVN inf_le_right
  rw [hbot, Subgroup.relIndex_bot_left] at hrel
  show Nat.card ↥(secImg (NV T V) (fsuV1 T V) Vp) = 4
  rw [hrel]
  have hcard : Nat.card ↥((fsuV1 T V).subgroupOf Vp) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV1).toEquiv, hc1]
  have hmul := Subgroup.card_mul_index ((fsuV1 T V).subgroupOf Vp)
  rw [hcard, hc3] at hmul
  show ((fsuV1 T V).subgroupOf Vp).index = 4
  omega

end L32HatC4

end CFSG.Quasithin.H13.A6
