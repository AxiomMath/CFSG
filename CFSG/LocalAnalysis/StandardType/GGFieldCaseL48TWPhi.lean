module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWWeyl
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped Pointwise commutatorElement

namespace GGL48TW

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_phi {p : ℕ} [hp : Fact p.Prime] {Bs X U U₁ : Subgroup G} {x : G}
    (h45 : GGL45Setup p Bs X U) (hΩ : ∀ u ∈ U, u ^ p = 1 → u ∈ Bs)
    (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hBs : Bs = (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x)
    (hNB : Subgroup.normalizer (Bs : Set G) ≤
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))
    (hNU : Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (U₁ : Set G))
    (hΦ : ∀ g ∈ Subgroup.centralizer
        ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      g ∈ Subgroup.normalizer (Bs : Set G) →
        x⁻¹ * (g * x * g⁻¹) ∈ Bs ⊓ Subgroup.centralizer (X : Set G)) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) ≤
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (U₁ : Set G)) ⊔
        Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨hUC, hUp, hUmax, hBU⟩ := h45
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set C := Subgroup.centralizer (B₁ : Set G) with hC
  set CB := Subgroup.centralizer (Bs : Set G) with hCB
  set D := C ⊓ Subgroup.normalizer (Bs : Set G) with hD
  have hxBs : x ∈ Bs := by rw [hBs]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hCBC : CB ≤ C := Subgroup.centralizer_le inf_le_left
  have hCBN : CB ≤ Subgroup.normalizer (Bs : Set G) := Subgroup.centralizer_le_normalizer _
  have hconjBs : ∀ u ∈ U, ∀ b ∈ Bs, u * b * u⁻¹ ∈ Bs := fun u hu b hb =>
    hΩ _ (U.mul_mem (U.mul_mem hu (hBU hb)) (U.inv_mem hu)) (by rw [conj_pow, hBp b hb]; group)
  have hUN : U ≤ Subgroup.normalizer (Bs : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨hconjBs u hu b, fun hb => ?_⟩
    have := hconjBs u⁻¹ (U.inv_mem hu) _ hb
    simpa [mul_assoc] using this
  have hUD : U ≤ D := le_inf hUC hUN
  have hpow : ∀ g ∈ D, g ^ p ∈ CB := by
    intro g hg
    obtain ⟨hgC, hgN⟩ := hg
    have hb := hΦ g hgC hgN
    set b := x⁻¹ * (g * x * g⁻¹) with hbdef
    have hgx : g * x * g⁻¹ = x * b := by rw [hbdef]; group
    have hgb : g * b * g⁻¹ = b := by
      have := Subgroup.mem_centralizer_iff.mp hgC b hb
      rw [← this]; group
    have hk : ∀ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = x * b ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ = g * (g ^ k * x * (g ^ k)⁻¹) * g⁻¹ := by group
          _ = g * (x * b ^ k) * g⁻¹ := by rw [ih]
          _ = (g * x * g⁻¹) * (g * b * g⁻¹) ^ k := by rw [conj_pow]; group
          _ = x * b ^ (k + 1) := by rw [hgx, hgb, pow_succ']; group
    have hbp : b ^ p = 1 := hBp b hb.1
    have hxc : g ^ p * x = x * g ^ p := by
      have := hk p
      rw [hbp, mul_one] at this
      calc g ^ p * x = g ^ p * x * (g ^ p)⁻¹ * g ^ p := by group
        _ = x * g ^ p := by rw [this]
    have hgpC : g ^ p ∈ C := C.pow_mem hgC p
    have hle : Bs ≤ Subgroup.centralizer ({g ^ p} : Set G) := by
      rw [hBs]
      refine sup_le (fun y hy => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hgpC y hy)
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hxc.symm
    rw [hCB, Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    exact this
  have hCBD : CB ≤ D := le_inf hCBC hCBN
  have hDN : D ≤ Subgroup.normalizer (CB : Set G) :=
    inf_le_right.trans (ggNormalizer_le_normalizer_centralizer Bs)
  haveI hnorm : (CB.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCBD).mpr hDN
  have hQp : IsPGroup p (D ⧸ CB.subgroupOf D) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hpow g g.2
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  have hidxCB : CB.relIndex D = p ^ k := hk
  let SUD : Sylow p D := GGL48.sylowSubgroupOf hUp hUD fun R hRD hRp hUR =>
    hUmax R (hRD.trans inf_le_left) hRp hUR
  have hndvd : ¬ p ∣ U.relIndex D := by
    have := SUD.not_dvd_index
    rwa [GGL48.coe_sylowSubgroupOf] at this
  have hd1 : (U ⊔ CB).relIndex D ∣ U.relIndex D := Subgroup.relIndex_dvd_of_le_left _ le_sup_left
  have hd2 : (U ⊔ CB).relIndex D ∣ p ^ k :=
    hidxCB ▸ Subgroup.relIndex_dvd_of_le_left _ le_sup_right
  have hd : (U ⊔ CB).relIndex D = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hd2
    rcases j with _ | j
    · simpa using hj
    · exact absurd (hj ▸ hd1 |> (dvd_pow_self p (Nat.succ_ne_zero j)).trans) hndvd
  have hDle : D ≤ U ⊔ CB := Subgroup.relIndex_eq_one.mp hd
  rintro n ⟨hnx, hnN⟩
  have hnB₁ := hNB hnN
  have hninv : ∀ b ∈ B₁, n⁻¹ * b * n ∈ B₁ := fun b hb => by
    have := (Subgroup.mem_normalizer_iff.mp hnB₁ (n⁻¹ * b * n)).mpr (by simpa [mul_assoc] using hb)
    exact this
  let U' := U.map (MulAut.conj n).toMonoidHom
  have hU'C : U' ≤ C := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hC, Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' := hninv b hb
    have hcomm := Subgroup.mem_centralizer_iff.mp (hUC hu) _ hb'
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc b * (n * u * n⁻¹) = n * ((n⁻¹ * b * n) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * b * n)) * n⁻¹ := by rw [hcomm]
      _ = n * u * n⁻¹ * b := by group
  let SU : Sylow p C := GGL48.sylowSubgroupOf hUp hUC fun R hRC hRp hUR => hUmax R hRC hRp hUR
  have hU'p : IsPGroup p (U'.subgroupOf C) :=
    (hUp.map _).comap_of_injective C.subtype C.subtype_injective
  obtain ⟨S, hS⟩ := hU'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C SU S
  have hconj : ∀ y ∈ U', ∃ u ∈ U, (g : G) * u * (g : G)⁻¹ = y := by
    intro y hy
    have hyS : (⟨y, hU'C hy⟩ : C) ∈ (S : Subgroup C) := hS (by simpa [Subgroup.mem_subgroupOf])
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyS
    obtain ⟨s, hs, hsy⟩ := hyS
    refine ⟨s, ?_, ?_⟩
    · have : s ∈ (SU : Subgroup C) := hs
      rw [GGL48.coe_sylowSubgroupOf, Subgroup.mem_subgroupOf] at this
      exact this
    · have := congrArg Subtype.val hsy
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hBsU' : ∀ b ∈ Bs, b ∈ U' := fun b hb => by
    have hb' : n⁻¹ * b * n ∈ Bs := by
      have := (Subgroup.mem_normalizer_iff.mp hnN (n⁻¹ * b * n)).mpr (by simpa [mul_assoc] using hb)
      exact this
    exact ⟨n⁻¹ * b * n, hBU hb', by simp [MulAut.conj_apply, mul_assoc]⟩
  have hginv : ∀ b ∈ Bs, (g : G)⁻¹ * b * (g : G) ∈ Bs := by
    intro b hb
    obtain ⟨s, hsU, hsb⟩ := hconj b (hBsU' b hb)
    have hs : (g : G)⁻¹ * b * (g : G) = s := by rw [← hsb]; group
    rw [hs]
    refine hΩ s hsU ?_
    have hb1 := hBp b hb
    rw [← hsb, conj_pow] at hb1
    have : s ^ p = (g : G)⁻¹ * ((g : G) * s ^ p * (g : G)⁻¹) * (g : G) := by group
    rw [this, hb1]; group
  have hmapLe : Bs.map (MulAut.conj (g : G)⁻¹).toMonoidHom ≤ Bs := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using hginv b hb
  have hmapEq : Bs.map (MulAut.conj (g : G)⁻¹).toMonoidHom = Bs :=
    Subgroup.eq_of_le_of_card_ge hmapLe (by
      rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)⁻¹).injective])
  have hgN : (g : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [← hmapEq] at hb
      obtain ⟨b₀, hb₀, hb₀b⟩ := hb
      have : (g : G) * b * (g : G)⁻¹ = b₀ := by
        rw [← hb₀b]; simp [MulAut.conj_apply]; group
      rw [this]; exact hb₀
    · intro hb
      have := hginv _ hb
      simpa [mul_assoc] using this
  have hgD : (g : G) ∈ D := ⟨g.2, hgN⟩
  have hUNCB : U ≤ Subgroup.normalizer (CB : Set G) := hUD.trans hDN
  have hgmem : (g : G) ∈ ((CB ⊔ U : Subgroup G) : Set G) := by
    have := hDle hgD
    rw [sup_comm] at this
    exact this
  rw [Subgroup.coe_mul_of_right_le_normalizer_left CB U hUNCB] at hgmem
  obtain ⟨h, hh, u, hu, hhu⟩ := hgmem
  have hU'le : U' ≤ U.map (MulAut.conj h).toMonoidHom := by
    intro y hy
    obtain ⟨s, hsU, hsy⟩ := hconj y hy
    refine ⟨u * s * u⁻¹, U.mul_mem (U.mul_mem hu hsU) (U.inv_mem hu), ?_⟩
    simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hsy, ← hhu]; group
  have hU'eq : U' = U.map (MulAut.conj h).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hU'le (by
      rw [Subgroup.card_map_of_injective (MulAut.conj h).injective,
        Subgroup.card_map_of_injective (MulAut.conj n).injective])
  set m := h⁻¹ * n with hm
  have hmU : m ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 : n * y * n⁻¹ ∈ U' := ⟨y, hy, by simp [MulAut.conj_apply]⟩
      rw [hU'eq] at h1
      obtain ⟨z, hz, hzy⟩ := h1
      simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      have : m * y * m⁻¹ = z := by
        rw [hm]
        calc h⁻¹ * n * y * (h⁻¹ * n)⁻¹ = h⁻¹ * (n * y * n⁻¹) * h := by group
          _ = h⁻¹ * (h * z * h⁻¹) * h := by rw [hzy]
          _ = z := by group
      rw [this]; exact hz
    · intro hy
      have h1 : h * (m * y * m⁻¹) * h⁻¹ ∈ U' := by
        rw [hU'eq]; exact ⟨_, hy, by simp [MulAut.conj_apply]⟩
      obtain ⟨z, hz, hzy⟩ := h1
      simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      have : z = y := by
        have hzy' : n * z * n⁻¹ = n * y * n⁻¹ := by rw [hzy, hm]; group
        simpa using hzy'
      rw [← this]; exact hz
  have hhC : h ∈ C := hCBC hh
  have hmx : m ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [hm]
    refine Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) hnx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hh x hxBs).symm
  have hmB₁ : m ∈ Subgroup.normalizer (B₁ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hhC)) hnB₁
  have hmU₁ : m ∈ Subgroup.normalizer (U₁ : Set G) := hNU ⟨hmU, hmB₁⟩
  have : n = h * m := by rw [hm]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left ⟨hmx, hmU₁⟩)

theorem phi_of_nbrField (hF : GGL48NbrFieldInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁) :
    ∀ g ∈ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      g ∈ Subgroup.normalizer (Bs : Set G) →
        x⁻¹ * (g * x * g⁻¹) ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
  intro g hgC hgN
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have hBp : ∀ b ∈ Bs, b ^ p = 1 := hS.1.1.2.1.2.1.2
  have hxQ := hF G p B Bs x L D J X B₂ d y K U U₁ hS
  obtain ⟨⟨-, hcan, hX1, hX2, hX3, hX4, hX5⟩, -, h43, -, -, h44, h45, hID, -⟩ := id hS
  obtain ⟨hDd, hd1, hNbr, hyd, -⟩ := h44
  obtain ⟨hUC, -, -, hBsU⟩ := h45
  have hdD : d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hDd]; exact Subgroup.mem_zpowers d
  have hcanK := hcan X hX1 hX2 hX3 hX4 hX5 d hdD hd1 y K hNbr hyd
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set N := Subgroup.normalizer (K : Set G) with hN
  have hCK : Subgroup.centralizer (B₁ : Set G) ≤ N := by
    intro g hg
    refine hcanK ⟨Subgroup.centralizer_le_normalizer _ hg, ?_⟩
    have hzle : Subgroup.zpowers d ≤ B₁ := by
      rw [Subgroup.zpowers_le]; exact hdD.2
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hzle hg)
  have hxBs : x ∈ Bs := by rw [h43.2]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxC : x ∈ Subgroup.centralizer (B₁ : Set G) := hUC (hBsU hxBs)
  set Q := ⁅N, N⁆ ⊔ U₁ with hQ
  set e := x⁻¹ * (g * x * g⁻¹) with he
  have heBs : e ∈ Bs :=
    Bs.mul_mem (Bs.inv_mem hxBs) ((Subgroup.mem_normalizer_iff.mp hgN x).mp hxBs)
  have heQ : e ∈ Q := by
    have : e = ⁅x⁻¹, g⁆ := by rw [commutatorElement_def, he]; group
    rw [this]
    exact Subgroup.mem_sup_left
      (Subgroup.commutator_mem_commutator (N.inv_mem (hCK hxC)) (hCK hgC))
  have hxB₁ : Subgroup.zpowers x ≤ Subgroup.normalizer (B₁ : Set G) := by
    rw [Subgroup.zpowers_le]; exact Subgroup.centralizer_le_normalizer _ hxC
  have hBsc : (Bs : Set G) = (Subgroup.zpowers x : Set G) * (B₁ : Set G) := by
    rw [h43.2, sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hxB₁]
  have heS : e ∈ (Subgroup.zpowers x : Set G) * (B₁ : Set G) := by
    rw [← hBsc]; exact heBs
  obtain ⟨a, ⟨j, rfl⟩, b, hb, hab⟩ := heS
  have hbU₁ : b ∈ U₁ := ((h46.2.2.2.1 b).mp hb).1
  have hxj : x ^ j ∈ Q := by
    have : x ^ j = e * b⁻¹ := by rw [← hab]; simp
    rw [this]; exact Q.mul_mem heQ (Q.inv_mem (Subgroup.mem_sup_right hbU₁))
  have hxp : x ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact hBp x hxBs
  have hdvd : (p : ℤ) ∣ j := by
    by_contra hnd
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime j (p : ℤ) :=
      (Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr hnd |>.symm
    obtain ⟨u, v, huv⟩ := hcop
    apply hxQ
    have : x = (x ^ j) ^ u * (x ^ (p : ℤ)) ^ v := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm j u, mul_comm (p : ℤ) v, huv, zpow_one]
    rw [this, hxp, one_zpow, mul_one]
    exact Q.zpow_mem hxj u
  obtain ⟨m, rfl⟩ := hdvd
  have : e = b := by
    rw [← hab]; simp only [zpow_mul, hxp, one_zpow, one_mul]
  rw [this]; exact hb

theorem inf_le_of_innerDiagPart (hsub : GGRawInnSubgroupInput) {U K U₁ : Subgroup G}
    (hID : GGInnerDiagPart U K U₁) : U ⊓ K ≤ U₁ := by
  obtain ⟨hUN, hle, hM⟩ := hID
  have hM1 := largeEvenMarking_and_labelAll_simple (S := fun _ => True) (P' := GGRawInnSubgroup)
    (fun lab hl _ => hsub lab hl) (fun _ _ _ _ _ _ _ => trivial) hM
  obtain ⟨-, lab, -, hraw⟩ := hM1
  obtain ⟨R, _, I, F, -, -, θ, hP, -, -, hinn⟩ := largeEvenRawDatum_exists hraw
  rintro u ⟨huU, huK⟩
  refine (hP u huU).mpr ⟨MulAut.conj (θ (QuotientGroup.mk (⟨u⁻¹, K.inv_mem huK⟩ : K))),
    hinn _, ?_⟩
  intro k k' h
  have : (k' : K) = ⟨u⁻¹, K.inv_mem huK⟩ * k * (⟨u⁻¹, K.inv_mem huK⟩ : K)⁻¹ := by
    apply Subtype.ext
    simp [h]
  rw [this]
  simp [MulAut.conj_apply]

end GGL48TW

theorem ggL48AutomizerFirst_of_nbrField {G : Type} [Group G] [Finite G] (hF : GGL48NbrFieldInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G} {d y : G}
    {K U U₁ : Subgroup G} (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (h46 : GGL46 p Bs x X U U₁) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) ≤
      ggL48H0 x U₁ ⊔ Subgroup.centralizer (Bs : Set G) := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBp : ∀ b ∈ Bs, b ^ p = 1 := hS.1.1.2.1.2.1.2
  obtain ⟨hFC, -, h43, -, -, -, h45, -, hNU⟩ := id hS
  obtain ⟨-, -, hXN, -, hXn, -, -⟩ := hFC
  have hNX : Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hXN
  have hNB : Subgroup.normalizer (Bs : Set G) ≤
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
    intro n hn
    have hnC := ggNormalizer_le_normalizer_centralizer X (hNX hn)
    rw [Subgroup.mem_normalizer_iff] at hn hnC ⊢
    intro b
    simp only [Subgroup.mem_inf]
    exact and_congr (hn b) (hnC b)
  exact GGL48TW.normalizer_le_of_phi h45 h46.2.2.2.2.1 hBp h43.2 hNB hNU
    (GGL48TW.phi_of_nbrField hF hS h46)

theorem ggL48InnerKInput_of_rawInnSubgroup (hsub : GGRawInnSubgroupInput) : GGL48InnerKInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS =>
    GGL48TW.inf_le_of_innerDiagPart hsub hS.2.2.2.2.2.2.2.1

theorem ggL48LFieldIOneInput_of_torusWeyl (hF : GGL48NbrFieldInput)
    (hT : GGL48TorusWeylCentInput) (hsub : GGNbrSubcomponentInput) (hUK : GGL48InnerKInput) :
    GGL48LFieldIOneInputS := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hI1
  have hJK : J ≤ K := hsub G p B x L D J hS.1.1.1 hS.1.1.2.2 y K hS.2.2.2.2.2.1.2.2.1
  exact not_mem_lField_of_torusWeyl hF hT hS hI1 hJK (hUK G p B Bs x L D J X B₂ d y K U U₁ hS)

end CFSG.StandardType
