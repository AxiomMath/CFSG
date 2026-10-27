module

public import CFSG.Quasithin.Vol2.Ch9KGFFSpPar
public import CFSG.Quasithin.Vol2.Ch9KGFFSplit
public import CFSG.Quasithin.Vol2.Ch9KGFFB51
public import CFSG.Quasithin.Vol2.Ch9KGFFSpKP

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Open hiding StatedSp StatedProj
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open scoped IsMulCommutative Matrix

section Tools

variable {G : Type} [Group G]

theorem commutator_le_map_modCommOf {U₀ U K : Subgroup G} [IsMulCommutative ↥U] (hU₀ : U₀ ≤ U)
    (hKN : K ≤ Subgroup.normalizer (U : Set G)) :
    ⁅U₀, K⁆ ≤ (modCommOf (autOn K U) (U₀.subgroupOf U)).map U.subtype := by
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have hkN := hKN hk
  set w : ↥U := ⟨u, hU₀ hu⟩ with hw
  set φ : MulAut ↥U := conjAct U ⟨k, hkN⟩ with hφ
  have hφK : φ ∈ autOn K U := Setup.mem_autOn_iff.mpr ⟨⟨k, hkN⟩, hk, rfl⟩
  have hwi : w⁻¹ ∈ U₀.subgroupOf U := by
    rw [Subgroup.mem_subgroupOf]
    exact U₀.inv_mem hu
  refine ⟨φ w⁻¹ * w⁻¹⁻¹, Subgroup.subset_closure ⟨φ, hφK, w⁻¹, hwi, rfl⟩, ?_⟩
  have h1 : ((φ w⁻¹ : ↥U) : G) = k * u⁻¹ * k⁻¹ := by
    rw [hφ, Setup.coe_conjAct_apply]
    rfl
  have hc : (φ w⁻¹ : ↥U) * w = w * φ w⁻¹ := mul_comm _ _
  have h2 : ((φ w⁻¹ : ↥U) : G) * u = u * ((φ w⁻¹ : ↥U) : G) := congrArg Subtype.val hc
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, inv_inv]
  rw [h2, h1, commutatorElement_def]
  group

variable [Finite G]

theorem pCoreOf_autOn_le {K U : Subgroup G} (hKN : K ≤ Subgroup.normalizer (U : Set G))
    (hC : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (U : Set G))) :
    pCoreOf 2 (autOn K U) ≤ autOn (pCoreOf 2 K) U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := InternalSec.autOnHom hKN with hρ
  set R : Subgroup ↥K := (CFSG.Open.pCore 2 ↥(autOn K U)).comap ρ with hR
  have hRn : R.Normal := (CFSG.LieType.BorelTits.pCore_normal 2).comap ρ
  have hRp : IsPGroup 2 ↥R := by
    intro r
    obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(autOn K U)) 2
      ⟨ρ r, r.2⟩
    have h1 : ρ ((r : ↥K) ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have h2 : ((r : ↥K) : G) ^ 2 ^ a ∈ K ⊓ Subgroup.centralizer (U : Set G) := by
      refine ⟨K.pow_mem (r : ↥K).2 _, ?_⟩
      have := (InternalSec.mem_ker_autOnHom hKN _).1 h1
      simpa using this
    obtain ⟨b, hb⟩ := hC ⟨_, h2⟩
    refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
    have h3 : (((r : ↥K) : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      simpa using congrArg Subtype.val hb
    simpa [pow_add, pow_mul] using h3
  have hRle : R ≤ CFSG.Open.pCore 2 ↥K := CFSG.LieType.BorelTits.le_pCore 2 hRn hRp
  rintro φ ⟨ψ₀, hψ₀, rfl⟩
  obtain ⟨r, hr⟩ := InternalSec.autOnHom_surjective hKN ψ₀
  have hrR : r ∈ R := by
    show ρ r ∈ CFSG.Open.pCore 2 ↥(autOn K U)
    rw [hr]
    exact hψ₀
  have hrO : (r : G) ∈ pCoreOf 2 K := ⟨r, hRle hrR, rfl⟩
  refine Setup.mem_autOn_iff.mpr ⟨⟨r, hKN r.2⟩, hrO, ?_⟩
  rw [← hr]
  rfl

end Tools

section Nat

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {Z : Subgroup V} {F : Type}
  [Field F]

theorem fixed_iff_of_realizes {π : ↥(StatedSp 2 F) →* ↥L}
    (hR : (FFModel.nat (StatedSp 2 F)).RealizesVia L (commV L) Z π) {x : V}
    (hx : x ∈ commV L) :
    ∃ w : Fin 2 ⊕ Fin 2 → F, ∀ γ : ↥(StatedSp 2 F),
      (((π γ : ↥L) : MulAut V) x * x⁻¹ ∈ Z ↔ spMat γ *ᵥ w = w) := by
  obtain ⟨β, -, hβk, hβe⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSp 2 F)) rfl rfl hR
  refine ⟨Multiplicative.toAdd (β ⟨x, hx⟩), fun γ => ?_⟩
  have hγx : ((π γ : ↥L) : MulAut V) x ∈ commV L := hR.2.2.2.1 (π γ) x hx
  have hmem : ((π γ : ↥L) : MulAut V) x * x⁻¹ ∈ commV L :=
    (commV L).mul_mem hγx ((commV L).inv_mem hx)
  have e1 : β ⟨_, hγx⟩ = (FFModel.nat (StatedSp 2 F)).act γ (β ⟨x, hx⟩) := hβe γ ⟨x, hx⟩ hγx
  have e2 : β ⟨_, hmem⟩ = β ⟨_, hγx⟩ * (β ⟨x, hx⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]
    rfl
  refine (hβk ⟨_, hmem⟩).symm.trans ?_
  rw [e2, e1, mul_inv_eq_one]
  constructor
  · intro h
    exact congrArg Multiplicative.toAdd h
  · intro h
    exact congrArg Multiplicative.ofAdd h

end Nat

section Main

variable {G : Type} [Group G] [Finite G]

theorem map_mem_normalizer_map {S M : Type*} [Group S] [Group M] (Φ : S →* M) {R : Subgroup S}
    {a : S} (h1 : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (h2 : ∀ r ∈ R, a⁻¹ * r * a ∈ R) :
    Φ a ∈ Subgroup.normalizer ((R.map Φ : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨a * r * a⁻¹, h1 r hr, by simp only [map_mul, map_inv]⟩
  · rintro ⟨r, hr, hrn⟩
    refine ⟨a⁻¹ * r * a, h2 r hr, ?_⟩
    rw [map_mul, map_mul, map_inv, hrn]
    group

theorem false_of_sp44
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) (h51 : AsB51) (h56 : AsB56)
    {Y T K KY U U₀ : Subgroup G} {v : G} (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y)
    (hKY : K ≤ Y) (hKl : K ∈ lFamily T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA5 : Nonempty (O2Q K ≃* alternatingGroup (Fin 5))) (hKYc : KY ∈ cComp Y) (hlt : K < KY)
    (hYKY : Y ≤ Subgroup.normalizer (KY : Set G)) (hred : IsTwoReducedIn Y U)
    (hJ : ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G))
    (hnK : ¬ KY ≤ K ⊔ (KY ⊓ Subgroup.centralizer (U : Set G))) (hSp : IsPSp4 2 2 (O2Q KY))
    (hU₀ : U₀ ≤ U) (hU₀K : U₀ ≤ ⁅U₀, K⁆) (hO2K : pCoreOf 2 K ≤ Subgroup.centralizer (U₀ : Set G))
    (hv : v ∈ U₀) (hv1 : v ≠ 1) (hKYv : KY ≤ Subgroup.centralizer ({v} : Set G)) : False := by
  have : IsMulCommutative ↥U := hred.2.2.1.1
  have hKYY : KY ≤ Y := le_of_mem_cComp hKYc
  have hKYN : KY ≤ Subgroup.normalizer (U : Set G) := hKYY.trans hred.2.1
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := hlt.le.trans hKYN
  have hKU : ¬ K ≤ Subgroup.centralizer (U : Set G) := by
    intro hKC
    have h0 : ⁅U₀, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_centralizer_iff.mp (hKC hk) u (hU₀ hu)).symm
    have := hU₀K hv
    rw [h0, Subgroup.mem_bot] at this
    exact hv1 this
  obtain ⟨-, hqA, -, -, -, -⟩ :=
    kyStar_cases h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt hYKY hred hJ hnK hKU
  obtain ⟨hC, -, -⟩ := sp44_facts hKYc hYKY hred hqA hSp
  rcases isIntDirect_or_natural_of_sp44 h51 h56 hSQ hT hKYc hYKY hred hJ hqA hSp with
    hdir | ⟨F, _, _, hF, πn, hR⟩
  · exact false_of_isIntDirect hKYN hlt.le hdir hU₀ hU₀K hv hv1 hKYv
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hFk : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨2, by rw [hF]; norm_num⟩
  have hK4 : ∃ s : Finset F, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (le_of_eq hF.symm)
  have hU3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have : Nontrivial Fˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hU3]
    norm_num
  obtain ⟨ω, hω1⟩ := exists_ne (1 : Fˣ)
  have hω : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
  have hω3 : ω ^ 3 = 1 := by
    rw [← hU3]
    exact pow_card_eq_one'
  set θ : ↥(StatedSp 2 F) ≃* ↥(autOn KY U) := MulEquiv.ofBijective πn
    ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hR, hR.1⟩ with hθ
  obtain ⟨P, hP, hKP⟩ := exists_parab_of_sp44 h36 h312 h314 h56 hSQ hT hKY hKl hTK hA5 hKYc hlt
    hYKY hred hJ hnK hKU hSp
  obtain ⟨g, j, hgj⟩ := exists_conj_of_parab hSQ hKYc hlt hYKY hred hKU hSp hFk θ hP hKP
  set Φ : ↥(StatedSp 2 F) →* MulAut ↥U :=
    (autOn KY U).subtype.comp (θ.toMonoidHom.comp (MulAut.conj g).toMonoidHom) with hΦ
  have hΦL : ∀ s, Φ s ∈ autOn KY U := fun s => (θ _).2
  have hΦπ : ∀ s, Φ s = ((πn (g * s * g⁻¹) : ↥(autOn KY U)) : MulAut ↥U) := fun s => rfl
  have hKstar : autOn K U = (perfectCore (Q2 F j)).map Φ := by
    have h1 := congrArg (Subgroup.map (autOn KY U).subtype) hgj
    rw [Subgroup.map_subgroupOf_eq_of_le (InternalSec.autOn_le_autOn_of_le hlt.le)] at h1
    rw [h1, Subgroup.map_map, Subgroup.map_map]
    rfl
  set Q : Subgroup (MulAut ↥U) := (SpM.rad j).map Φ with hQ
  set h : MulAut ↥U := Φ (SpM.hEl ω j) with hh
  have hQK : Q ≤ autOn K U := by
    rw [hKstar]
    exact Subgroup.map_mono (SpM.rad_le j)
  have hQO : Q ≤ pCoreOf 2 (autOn K U) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 hQK ?_ ((SpM.rad_isPGroup hFk j).map Φ)
    rw [Subgroup.normal_subgroupOf_iff hQK]
    intro q k hq hk
    rw [hKstar] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    obtain ⟨r, hr, rfl⟩ := hq
    exact ⟨n * r * n⁻¹, SpM.conj_mem_rad hn hr, by simp only [map_mul, map_inv]⟩
  have hO2 := pCoreOf_autOn_le hKN (hC.to_le (inf_le_inf_right _ hlt.le))
  have hU₀Q : ∀ q ∈ Q, ∀ u ∈ U₀.subgroupOf U, q u = u := by
    intro q hq u hu
    obtain ⟨k, hk, hkq⟩ := Setup.mem_autOn_iff.mp (hO2 (hQO hq))
    rw [← hkq]
    apply Subtype.ext
    rw [Setup.coe_conjAct_apply]
    have hku := Subgroup.mem_centralizer_iff.mp (hO2K hk) u hu
    rw [← hku, mul_inv_cancel_right]
  have hV : ∀ x : ↥U, x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa [sq] using hred.2.2.1.2 x x.2)
  have hKL : autOn K U ≤ autOn KY U := InternalSec.autOn_le_autOn_of_le hlt.le
  have h3 : h ^ 3 = 1 := by rw [hh, ← map_pow, SpM.hEl_pow_three hω3, map_one]
  have hhQ : h ∈ Subgroup.normalizer (Q : Set (MulAut ↥U)) :=
    map_mem_normalizer_map Φ (fun r hr => SpM.conj_hEl_mem_rad ω j hr)
      (fun r hr => SpM.conj_hEl_inv_mem_rad hω3 j hr)
  have hKQ : autOn K U ≤ Subgroup.normalizer (Q : Set (MulAut ↥U)) := by
    rw [hKstar]
    rintro _ ⟨n, hn, rfl⟩
    refine map_mem_normalizer_map Φ (fun r hr => SpM.conj_mem_rad hn hr) (fun r hr => ?_)
    have := SpM.conj_mem_rad ((perfectCore (Q2 F j)).inv_mem hn) hr
    rwa [inv_inv] at this
  have hhK : ∀ k ∈ autOn K U, h * k * h⁻¹ * k⁻¹ ∈ Q := by
    rw [hKstar]
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨_, SpM.comm_hEl_mem_rad ω j hn, by simp only [hh, map_mul, map_inv]⟩
  have hKP : ∀ x ∈ commV (autOn KY U), (∀ q ∈ Q, q x = x) → h x = x →
      ∀ k ∈ autOn K U, k x * x⁻¹ ∈ fixV (autOn KY U) := by
    intro x hx hxQ hxh k hk
    obtain ⟨w, hw⟩ := fixed_iff_of_realizes hR hx
    have hfix : ∀ s, Φ s x = x → spMat s *ᵥ (spMat g⁻¹ *ᵥ w) =
        spMat g⁻¹ *ᵥ w := by
      intro s hs
      refine (SpM.conj_fixed_iff g s w).mp ((hw (g * s * g⁻¹)).mp ?_)
      rw [← hΦπ, hs, mul_inv_cancel]
      exact Subgroup.one_mem _
    rw [hKstar] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    have hn' := SpM.fixed_of_rad hK4 hω j (fun r hr => hfix r (hxQ _ ⟨r, hr, rfl⟩)) (hfix _ hxh) hn
    have h1 := (hw (g * n * g⁻¹)).mpr ((SpM.conj_fixed_iff g n w).mpr hn')
    rw [← hΦπ] at h1
    exact h1.1
  have hU₀K' : U₀.subgroupOf U ≤ modCommOf (autOn K U) (U₀.subgroupOf U) := by
    intro u hu
    obtain ⟨y, hy, hyu⟩ := commutator_le_map_modCommOf hU₀ hKN (hU₀K hu)
    rwa [Subtype.ext hyu] at hy
  have hbot := inf_fixV_eq_bot_of_split hV hKL (hΦL _) h3 hhQ hKQ hhK hKP hU₀K' hU₀Q
  have hvU : v ∈ U := hU₀ hv
  have h2' : (⟨v, hvU⟩ : ↥U) ∈ fixV (autOn KY U) := by
    rw [FFD.fixV_autOn_eq hKYN, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKYv hk) v rfl).symm
  have h2 : (⟨v, hvU⟩ : ↥U) ∈ U₀.subgroupOf U ⊓ fixV (autOn KY U) := ⟨hv, h2'⟩
  rw [hbot, Subgroup.mem_bot] at h2
  exact hv1 (congrArg Subtype.val h2)

end Main

end CFSG.Quasithin.H13.Ch9.KGFF
