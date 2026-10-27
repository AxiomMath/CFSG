module

public import CFSG.RankThree.PartOne.K1214.Center
import CFSG.RankThree.PartOne.S12.Sec127
import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S9.Vanishing.Basic
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {b : G} {K I X P Q : Subgroup G}

theorem centralizes_of_pElement (hp : p.Prime)
    (hnH : ¬ p ∣ Nat.card ↥(torusImage E (cNormalizer c))) {y : G}
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) (hyH : y ∈ cNormalizer c)
    (hyp : ∃ m : ℕ, y ^ (p ^ m) = 1) : ∀ e ∈ E, y * e * y⁻¹ = e := by
  obtain ⟨m, hm⟩ := hyp
  set γ : ↥(torusImage E (cNormalizer c)) :=
    ⟨E.normalizerMonoidHom ⟨y, hyN⟩, Subgroup.mem_map.2 ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.2 hyH,
      rfl⟩⟩ with hγ
  have hγpow : γ ^ (p ^ m) = 1 := by
    apply Subtype.ext
    show (E.normalizerMonoidHom ⟨y, hyN⟩) ^ (p ^ m) = 1
    rw [← map_pow]
    have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (p ^ m) = 1 := Subtype.ext hm
    rw [this, map_one]
  have hγ1 : γ = 1 := Sec12Fus.eq_one_of_pow_eq_one_of_not_dvd hp hnH hγpow
  have hγ1' : E.normalizerMonoidHom ⟨y, hyN⟩ = 1 := congrArg Subtype.val hγ1
  intro e he
  have h3 := Equivariance.coe_conjAut hyN ⟨e, he⟩
  have h4 : (conjAut E y hyN) ⟨e, he⟩ = ⟨e, he⟩ := by
    have : conjAut E y hyN = 1 := hγ1'
    rw [this]
    rfl
  rw [h4] at h3
  exact h3.symm

omit [Finite G] in
theorem le_normalizer_centralizer_of_le_normalizer {P E : Subgroup G}
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) :
    P ≤ Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) := by
  intro x hx
  have h1 : conjBy x (Subgroup.centralizer (E : Set G)) = Subgroup.centralizer (E : Set G) := by
    rw [← Equivariance.centralizer_conjBy, Equivariance.conjBy_eq_of_mem_normalizer (hPE hx)]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have h2 : x * g * x⁻¹ ∈ conjBy x (Subgroup.centralizer (E : Set G)) ↔
      g ∈ Subgroup.centralizer (E : Set G) := by
    rw [Equivariance.mem_conjBy]
    simp [mul_assoc]
  rw [h1] at h2
  exact h2.symm

theorem kf1214HSyl_of_u5 (hU5 : KF1214U5) : KF1214HSyl := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hc
  classical
  have hp : p.Prime := ctx.hyp.prime
  have : Fact p.Prime := ⟨hp⟩
  have hn12 : ¬ RowModel p L 12 := hU5 G p A c L E ctx
  have hnH := not_dvd_torusImage ctx hn12
  have hPE := P_le_normalizer_of_omega hc.omega
  have hEP := E_le_P hC
  have hcE := c_mem_E ctx
  have hbE : b ∈ E := ctx.hyp.A_le_E hL.b_mem.1
  have hPp : IsPGroup p ↥P := hC.P_sylow.1.2.1
  have hpow : ∀ x ∈ P, ∃ m : ℕ, x ^ (p ^ m) = 1 := fun x hx => by
    obtain ⟨m, hm⟩ := hPp ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  have hEH : E ≤ cNormalizer c := E_le_cNormalizer ctx.hyp
  set H := cNormalizer c with hH
  set CG := Subgroup.centralizer (E : Set G) with hCG
  have hPH : P ⊓ H = P ⊓ CG := by
    ext x
    constructor
    · rintro ⟨hxP, hxH⟩
      refine ⟨hxP, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
      have h1 := centralizes_of_pElement hp hnH (hPE hxP) hxH (hpow x hxP) e he
      calc e * x = (x * e * x⁻¹) * x := by rw [h1]
        _ = x * e := by group
    · rintro ⟨hxP, hxC⟩
      refine ⟨hxP, ?_⟩
      apply Sec127.mem_cNormalizer_of_conj_mem
      have h1 : c * x = x * c := Subgroup.mem_centralizer_iff.1 hxC c hcE
      have : x * c * x⁻¹ = c := by
        calc x * c * x⁻¹ = (c * x) * x⁻¹ := by rw [h1]
          _ = c := by group
      rw [this]
      exact Subgroup.mem_zpowers c
  have hCGb : CG ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (by simpa using hbE)
  have hPN : P ≤ Subgroup.normalizer (CG : Set G) := le_normalizer_centralizer_of_le_normalizer hPE
  have hsylCG : ABGLocalTools.IsSylowOf p (P ⊓ CG) CG :=
    inf_isSylowOf_of_le_normalizer (Vanish.isSylowOf_iff_abg.mp hC.P_sylow.1) hCGb hPN
  have hsylCG' : IsSylowOf p (P ⊓ CG) CG := Vanish.isSylowOf_iff_abg.mpr hsylCG
  have hCp : IsPGroup p ↥(P ⊓ H) := hPp.to_le inf_le_left
  refine ⟨inf_le_right, hCp, ?_⟩
  have hC'p : IsPGroup p ↥((P ⊓ H).subgroupOf H) :=
    hCp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨S, hCS⟩ := hC'p.exists_le_sylow
  set S1 : Subgroup G := (S : Subgroup ↥H).map H.subtype with hS1
  have hCS1 : P ⊓ H ≤ S1 := fun x hx => ⟨⟨x, hx.2⟩, hCS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hS1p : IsPGroup p ↥S1 := S.isPGroup'.map H.subtype
  have hS1H : S1 ≤ H := Subgroup.map_subtype_le _
  have hS1le : S1 ≤ P ⊓ H := by
    by_contra hne
    have hne' : P ⊓ H ≠ S1 := fun h => hne (h ▸ le_rfl)
    obtain ⟨y, hyS, hyC, hyN⟩ := Sec12Fus.exists_mem_normalizer_sdiff hCS1 hS1p hne'
    have hyH : y ∈ H := hS1H hyS
    obtain ⟨m, hm⟩ := hS1p ⟨y, hyS⟩
    have hyp : y ^ (p ^ m) = 1 := congrArg Subtype.val hm
    have hom : omegaOne p (P ⊓ H) = E := by
      apply le_antisymm
      · refine (Subgroup.closure_le _).2 ?_
        rintro x ⟨hx, hxp⟩
        rw [← hc.omega]
        exact Subgroup.subset_closure ⟨hx.1, hxp⟩
      · intro e he
        exact Subgroup.subset_closure ⟨⟨hEP he, hEH he⟩,
          Sec12Three.pow_eq_one_of_mem_E ctx.hyp he⟩
    have hyNE : y ∈ Subgroup.normalizer (E : Set G) := by
      have := Sec12Fus.mem_normalizer_omegaOne (p := p) hyN
      rwa [hom] at this
    have hycent := centralizes_of_pElement hp hnH hyNE hyH ⟨m, hyp⟩
    have hyCG : y ∈ CG := by
      refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
      calc e * y = (y * e * y⁻¹) * y := by rw [hycent e he]
        _ = y * e := by group
    have hpP : IsPGroup p ↥((P ⊓ CG).subgroupOf CG) :=
      (hPp.to_le (inf_le_left : P ⊓ CG ≤ P)).of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hidx' : ¬ p ∣ ((P ⊓ CG).subgroupOf CG).index := hsylCG'.2.2
    let Q' : Sylow p ↥CG := hpP.toSylow hidx'
    let yC : ↥CG := ⟨y, hyCG⟩
    have hzp : IsPGroup p (Subgroup.zpowers yC) := by
      intro x
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 x.2
      refine ⟨m, Subtype.ext ?_⟩
      have h5 : yC ^ (p ^ m) = 1 := Subtype.ext hyp
      rw [Subgroup.coe_pow]
      show (x : ↥CG) ^ (p ^ m) = 1
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5, one_zpow]
    have hinf := hzp.inf_normalizer_sylow Q'
    have hyN' : y ∈ Subgroup.normalizer ((P ⊓ CG : Subgroup G) : Set G) := by
      rw [← hPH]
      exact hyN
    have hyCN : yC ∈ Subgroup.normalizer
        (((P ⊓ CG).subgroupOf CG : Subgroup ↥CG) : Set ↥CG) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.1 hyN' (g : G)
    have hmem : yC ∈ Subgroup.zpowers yC ⊓ Subgroup.normalizer (Q' : Set ↥CG) :=
      ⟨Subgroup.mem_zpowers yC, hyCN⟩
    rw [hinf] at hmem
    have hyPC : y ∈ P ⊓ CG := hmem.2
    exact hyC (hPH ▸ hyPC)
  have hSle : (S : Subgroup ↥H) ≤ (P ⊓ H).subgroupOf H := fun h hh =>
    Subgroup.mem_subgroupOf.2 (hS1le ⟨h, hh, rfl⟩)
  have heq : (P ⊓ H).subgroupOf H = (S : Subgroup ↥H) := le_antisymm hCS hSle
  have hSidx := S.not_dvd_index
  show ¬ p ∣ ((P ⊓ H).subgroupOf H).index
  rw [heq]
  exact hSidx

end CFSG.RankThree.PartOne.K1214
