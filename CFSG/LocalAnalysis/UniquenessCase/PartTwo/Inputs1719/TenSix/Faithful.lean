module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Skeleton
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

private theorem conj_range_normal {L : Type*} [Group L] :
    (MulAut.conj : L →* MulAut L).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨x, rfl⟩ := hn
  refine ⟨g x, ?_⟩
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem centralizer_conj_range_eq_bot {L : Type*} [Group L] (hL : Group.IsPerfect L) :
    Subgroup.centralizer ((MulAut.conj : L →* MulAut L).range : Set (MulAut L)) = ⊥ := by
  refine eq_bot_iff.mpr fun β hβ => ?_
  rw [Subgroup.mem_bot]
  exact CFSG.QuasithinUnique.Setup.Layer.eq_one_of_commute_inner hL β fun x =>
    (Subgroup.mem_centralizer_iff.mp hβ (MulAut.conj x) ⟨x, rfl⟩).symm

theorem exists_faithful_pSubgroup {G : Type} [Group G] [Finite G] {L A X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hLq : IsQuasisimple ↥L)
    (hBT : HoldsTits (↥L ⧸ Subgroup.center ↥L) p) (hRR : RadRigid p (↥L ⧸ Subgroup.center ↥L))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hAp : Nat.Coprime (Nat.card A) p)
    (hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hXL : X ≤ L) (hXp : IsPGroup p ↥X) (hXZ : ¬ X ≤ (Subgroup.center ↥L).map L.subtype)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ∃ R : Subgroup G, R ≤ L ∧ IsPGroup p ↥R ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
      A ⊓ Subgroup.centralizer (R : Set G) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let c : ↥L →* MulAut ↥L := MulAut.conj
  let S : Subgroup (MulAut ↥L) := c.range
  have hSnormal : S.Normal := conj_range_normal
  have hSnormalI : S.Normal := hSnormal
  have hker : c.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker, CFSG.QuasithinUnique.Setup.Layer.conj_eq_one_iff]
  have he : (↥L ⧸ Subgroup.center ↥L) ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans (QuotientGroup.quotientKerEquivRange c)
  have hBT' : HoldsTits ↥S p := HoldsTits.of_mulEquiv he hBT
  have hRR' : RadRigid p ↥S := RadRigid.of_mulEquiv he hRR
  have hcentS : Subgroup.centralizer (S : Set (MulAut ↥L)) = ⊥ :=
    centralizer_conj_range_eq_bot hLq.1
  let ι : ↥A →* MulAut ↥L := (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hAL)
  have ι_coe : ∀ (a : ↥A) (x : ↥L), (((ι a) x : ↥L) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
    intro a x
    change ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion hAL a)) x : G) =
      (a : G) * (x : G) * (a : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hιker : ι.ker = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    rw [Subgroup.mem_bot]
    have hmemC : (a : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun β : MulAut ↥L => (((β ⟨x, hx⟩ : ↥L)) : G)) ha
      simp only [MulAut.one_apply] at h
      rw [ι_coe] at h
      calc (x : G) * (a : G) = (a : G) * (x : G) * (a : G)⁻¹ * (a : G) := by rw [h]
        _ = (a : G) * (x : G) := by group
    have hmem : (a : G) ∈ A ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_inf.mpr ⟨a.2, hmemC⟩
    rw [hAC] at hmem
    exact Subtype.ext (by simpa using hmem)
  have ι_inj : Function.Injective ι := (MonoidHom.ker_eq_bot_iff ι).mp hιker
  have ι_conj : ∀ (a : ↥A) (x : ↥L), ι a * c x * (ι a)⁻¹ = c (ι a x) := by
    intro a x
    ext y
    simp only [c, MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  let X' : Subgroup ↥L := X.subgroupOf L
  have hX'p : IsPGroup p ↥X' := hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXL).symm
  let Q : Subgroup (MulAut ↥L) := X'.map c
  have hQleS : Q ≤ S := Subgroup.map_le_range c X'
  have hQp : IsPGroup p ↥Q := hX'p.map c
  have hQne : Q ≠ ⊥ := by
    intro hbot
    apply hXZ
    have h1 : X' ≤ Subgroup.center ↥L := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff X').mp hbot
    have hXeq : X = X'.map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hXL).symm
    rw [hXeq]
    exact Subgroup.map_mono h1
  have hιX : ∀ a : ↥A, X'.map (ι a).toMonoidHom = X' := by
    intro a
    refine le_antisymm ?_ ?_
    · rintro z ⟨x, hx, rfl⟩
      show (((ι a) x : ↥L) : G) ∈ X
      rw [ι_coe]
      exact (Subgroup.mem_normalizer_iff.mp (hAX a.2) (x : G)).mp hx
    · intro z hz
      have hstep : (ι a⁻¹) z ∈ X' := by
        show (((ι a⁻¹) z : ↥L) : G) ∈ X
        rw [ι_coe]
        exact (Subgroup.mem_normalizer_iff.mp (hAX (a⁻¹).2) (z : G)).mp hz
      refine ⟨(ι a⁻¹) z, hstep, ?_⟩
      show (ι a) ((ι a⁻¹) z) = z
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hιQ : ∀ a : ↥A, ∀ q ∈ Q, ι a * q * (ι a)⁻¹ ∈ Q := by
    rintro a q ⟨x, hx, rfl⟩
    rw [ι_conj]
    refine Subgroup.mem_map_of_mem c ?_
    rw [← hιX a]
    exact Subgroup.mem_map_of_mem (ι a).toMonoidHom hx
  let T : Subgroup (MulAut ↥L) := ι.range
  let Γ : Subgroup (MulAut ↥L) := S ⊔ T
  have hSleΓ : S ≤ Γ := le_sup_left
  have hTleΓ : T ≤ Γ := le_sup_right
  have hQleΓ : Q ≤ Γ := hQleS.trans hSleΓ
  have hιmemΓ : ∀ a : ↥A, ι a ∈ Γ := fun a =>
    hTleΓ (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  let S' : Subgroup ↥Γ := S.subgroupOf Γ
  let Q' : Subgroup ↥Γ := Q.subgroupOf Γ
  have hS'normal : S'.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSleΓ,
      Subgroup.normalizer_eq_top_iff.mpr hSnormal]
    exact le_top
  have hS'normalI : S'.Normal := hS'normal
  have hBT'' : HoldsTits ↥S' p :=
    HoldsTits.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSleΓ).symm hBT'
  have hRR'' : RadRigid p ↥S' :=
    RadRigid.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSleΓ).symm hRR'
  have hCΓ : Subgroup.centralizer (S' : Set ↥Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro γ hγ
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hγ' : (γ : MulAut ↥L) ∈ Subgroup.centralizer (S : Set (MulAut ↥L)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hγ (⟨s, hSleΓ hs⟩ : ↥Γ) hs)
    rw [hcentS, Subgroup.mem_bot] at hγ'
    exact hγ'
  have hQ'p : IsPGroup p ↥Q' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQleΓ).symm
  have hQ'ne : Q' ≠ ⊥ := by
    intro hbot
    apply hQne
    have h : Q'.map (Subgroup.subtype Γ) = ⊥ := by rw [hbot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le hQleΓ] at h
  have hQ'le : Q' ≤ S' := fun x hx => hQleS hx
  have hlieQ := lieQ_of_radRigid S' hBT'' hRR'' hCΓ hQ'le hQ'ne hQ'p
  let M : Subgroup ↥Γ := Subgroup.normalizer (Q' : Set ↥Γ)
  let P : Subgroup ↥Γ := pCoreOf p M
  have hPp : IsPGroup p ↥P := pCoreOf_isPGroup p M
  have hιNQ : ∀ a : ↥A, (⟨ι a, hιmemΓ a⟩ : ↥Γ) ∈ M := by
    intro a
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have h1 : ι a * (q : MulAut ↥L) * (ι a)⁻¹ ∈ Q := hιQ a (q : MulAut ↥L) hq
      exact h1
    · intro hq
      have hqQ : ι a * (q : MulAut ↥L) * (ι a)⁻¹ ∈ Q := hq
      have h2 : ι a⁻¹ * (ι a * (q : MulAut ↥L) * (ι a)⁻¹) * (ι a⁻¹)⁻¹ ∈ Q :=
        hιQ a⁻¹ _ hqQ
      have h4 : ι a⁻¹ * (ι a * (q : MulAut ↥L) * (ι a)⁻¹) * (ι a⁻¹)⁻¹ =
          (q : MulAut ↥L) := by
        rw [map_inv]
        group
      rwa [h4] at h2
  have hιNP : ∀ a : ↥A, (⟨ι a, hιmemΓ a⟩ : ↥Γ) ∈ Subgroup.normalizer (P : Set ↥Γ) :=
    fun a => le_normalizer_pCoreOf p M (hιNQ a)
  have hPleS' : P ≤ S' := by
    let π : ↥Γ →* ↥Γ ⧸ S' := QuotientGroup.mk' S'
    have hPimp : IsPGroup p ↥(P.map π) := hPp.map π
    have hTcard : Nat.card ↥T = Nat.card ↥A := by
      have hT : T = Subgroup.map ι (⊤ : Subgroup ↥A) := by
        show ι.range = _
        rw [MonoidHom.range_eq_map]
      rw [hT, Subgroup.card_map_of_injective ι_inj, Subgroup.card_top]
    have hcard : Nat.card (↥Γ ⧸ S') ∣ Nat.card ↥A := by
      rw [← Subgroup.index_eq_card S']
      have hidx : S'.index = S.relIndex Γ := by
        rw [← Subgroup.relIndex_top_right (H := S')]
        have htop : Γ.subgroupOf Γ = (⊤ : Subgroup ↥Γ) := by ext x; simp
        rw [← htop]
        exact Subgroup.relIndex_subgroupOf le_rfl
      rw [hidx]
      have hsup : S.relIndex Γ = S.relIndex T := by
        have hΓ : Γ = T ⊔ S := by rw [sup_comm]
        rw [hΓ]
        exact Subgroup.relIndex_sup_right T S
      rw [hsup]
      refine dvd_trans (Subgroup.relIndex_dvd_card S T) ?_
      rw [hTcard]
    have hcop : Nat.Coprime (Nat.card (↥Γ ⧸ S')) p :=
      Nat.Coprime.coprime_dvd_left hcard hAp
    have hPimcop : Nat.Coprime (Nat.card ↥(P.map π)) p := by
      refine Nat.Coprime.coprime_dvd_left ?_ hcop
      have h := Subgroup.card_dvd_of_le (H := P.map π)
        (K := (⊤ : Subgroup (↥Γ ⧸ S'))) le_top
      rwa [Subgroup.card_top] at h
    have hPimtriv : P.map π = ⊥ := by
      rcases hPimp.card_eq_or_dvd with h | h
      · exact Subgroup.eq_bot_of_card_eq (H := P.map π) h
      · exact absurd h ((hp.coprime_iff_not_dvd).mp hPimcop.symm)
    intro x hx
    have hx' : π x ∈ P.map π := Subgroup.mem_map_of_mem π hx
    rw [hPimtriv] at hx'
    have hx1 : π x = 1 := by simpa using hx'
    have hxker : x ∈ π.ker := MonoidHom.mem_ker.mpr hx1
    rwa [QuotientGroup.ker_mk'] at hxker
  let P₁ : Subgroup (MulAut ↥L) := P.map (Subgroup.subtype Γ)
  have hP₁leS : P₁ ≤ S := by
    rintro x ⟨q, hq, rfl⟩
    exact hPleS' hq
  have hP₁p : IsPGroup p ↥P₁ := hPp.map (Subgroup.subtype Γ)
  let Rhat : Subgroup ↥L := P₁.comap c
  let φ : ↥Rhat →* ↥P₁ :=
    { toFun := fun x => ⟨c (x : ↥L), x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hφsurj : Function.Surjective φ := by
    intro y
    have hyS : (y : MulAut ↥L) ∈ S := hP₁leS y.2
    obtain ⟨x, hx⟩ := hyS
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show c x ∈ P₁
      rw [hx]
      exact y.2
    · exact Subtype.ext hx
  have hφker : φ.ker ≤ Subgroup.center ↥Rhat := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : c (x : ↥L) = 1 := congrArg Subtype.val hx
    have hxc : (x : ↥L) ∈ Subgroup.center ↥L :=
      (CFSG.QuasithinUnique.Setup.Layer.conj_eq_one_iff (x : ↥L)).mp hx1
    exact Subgroup.mem_center_iff.mp hxc (y : ↥L)
  have hP₁nil : Group.IsNilpotent ↥P₁ := hP₁p.isNilpotent
  have hRhatnil : Group.IsNilpotent ↥Rhat :=
    Subgroup.isNilpotent_of_ker_le_center φ hφker
  obtain ⟨R₀syl⟩ := (inferInstance : Nonempty (Sylow p ↥Rhat))
  have hR₀normal : (R₀syl : Subgroup ↥Rhat).Normal :=
    Group.IsNilpotent.sylow_normal hRhatnil p R₀syl
  have hR₀normalI : (R₀syl : Subgroup ↥Rhat).Normal := hR₀normal
  have hm_notdvd : ¬ p ∣ (R₀syl : Subgroup ↥Rhat).index := Sylow.not_dvd_index R₀syl
  let K : Subgroup ↥L := pCoreOf p Rhat
  have hKp : IsPGroup p ↥K := pCoreOf_isPGroup p Rhat
  have hKle : K ≤ Rhat := pCoreOf_le p Rhat
  have hpCoreEq : CFSG.pCore p ↥Rhat = (R₀syl : Subgroup ↥Rhat) := by
    have h1 : CFSG.pCore p ↥Rhat ≤ (R₀syl : Subgroup ↥Rhat) := by
      have : Unique (Sylow p ↥Rhat) := Sylow.unique_of_normal R₀syl hR₀normal
      obtain ⟨Q, hQ⟩ := (CFSG.pCore_isPGroup (p := p) (G := ↥Rhat)).exists_le_sylow
      have hQe : Q = R₀syl := Subsingleton.elim Q R₀syl
      rwa [hQe] at hQ
    exact le_antisymm h1 (CFSG.LieType.BorelTits.le_pCore p hR₀normal R₀syl.isPGroup')
  have hKchar : K = (R₀syl : Subgroup ↥Rhat).map Rhat.subtype := by
    show pCoreOf p Rhat = _
    rw [show pCoreOf p Rhat = (CFSG.pCore p ↥Rhat).map Rhat.subtype from rfl, hpCoreEq]
  have hcK : K.map c = P₁ := by
    refine le_antisymm ?_ ?_
    · rintro z ⟨x, hx, rfl⟩
      exact hKle hx
    · intro y hy
      obtain ⟨x, hx⟩ := hP₁leS hy
      have hxR : x ∈ Rhat := by
        show c x ∈ P₁
        rw [hx]
        exact hy
      let m := (R₀syl : Subgroup ↥Rhat).index
      have hxdvd : ¬ p ∣ m := by simpa [m] using hm_notdvd
      have hxpow : x ^ m ∈ K := by
        have h1 : (⟨x, hxR⟩ : ↥Rhat) ^ m ∈ (R₀syl : Subgroup ↥Rhat) :=
          Subgroup.pow_index_mem (R₀syl : Subgroup ↥Rhat) ⟨x, hxR⟩
        have h2 : (((⟨x, hxR⟩ : ↥Rhat) ^ m : ↥Rhat) : ↥L) ∈
            (R₀syl : Subgroup ↥Rhat).map Rhat.subtype :=
          Subgroup.mem_map_of_mem Rhat.subtype h1
        rw [hKchar]
        exact h2
      have hym : y ^ m ∈ K.map c := by
        refine ⟨x ^ m, hxpow, ?_⟩
        rw [map_pow, hx]
      obtain ⟨k, hk⟩ := hP₁p.exists_card_eq
      have hord : orderOf y ∣ p ^ k := by
        rw [← hk]
        exact Subgroup.orderOf_dvd_natCard P₁ hy
      have hcopm : Nat.Coprime m (orderOf y) := by
        have h1 : Nat.Coprime m p := ((hp.coprime_iff_not_dvd).mpr hxdvd).symm
        exact (h1.pow_right k).coprime_dvd_right hord
      obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hcopm
      rw [← ha]
      exact Subgroup.pow_mem _ hym a
  have hιP₁ : ∀ a : ↥A, (ι a) ∈ Subgroup.normalizer (P₁ : Set (MulAut ↥L)) := by
    intro a
    have h : (⟨ι a, hιmemΓ a⟩ : ↥Γ) ∈ Subgroup.normalizer (P : Set ↥Γ) := hιNP a
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h ⊢
    have h' : Subgroup.map (MulEquiv.toMonoidHom
        (MulAut.conj (⟨ι a, hιmemΓ a⟩ : ↥Γ))) P = P := h
    have hcomp : ((MulAut.conj (ι a)).toMonoidHom.comp (Subgroup.subtype Γ)) =
        ((Subgroup.subtype Γ).comp
          (MulAut.conj (⟨ι a, hιmemΓ a⟩ : ↥Γ)).toMonoidHom) := rfl
    calc P₁.map (MulAut.conj (ι a)).toMonoidHom
        = (P.map (Subgroup.subtype Γ)).map (MulAut.conj (ι a)).toMonoidHom := rfl
      _ = P.map ((MulAut.conj (ι a)).toMonoidHom.comp (Subgroup.subtype Γ)) :=
            Subgroup.map_map P _ _
      _ = P.map ((Subgroup.subtype Γ).comp
            (MulAut.conj (⟨ι a, hιmemΓ a⟩ : ↥Γ)).toMonoidHom) := by rw [hcomp]
      _ = (P.map (MulAut.conj (⟨ι a, hιmemΓ a⟩ : ↥Γ)).toMonoidHom).map
            (Subgroup.subtype Γ) := (Subgroup.map_map P _ _).symm
      _ = P.map (Subgroup.subtype Γ) := by rw [h']
      _ = P₁ := rfl
  have hιRhat : ∀ a : ↥A, Rhat.map (ι a).toMonoidHom = Rhat := by
    intro a
    refine le_antisymm ?_ ?_
    · rintro z ⟨y, hy, rfl⟩
      show c ((ι a) y) ∈ P₁
      have h1 : ι a * c y * (ι a)⁻¹ ∈ P₁ :=
        (Subgroup.mem_normalizer_iff.mp (hιP₁ a) (c y)).mp hy
      rwa [ι_conj] at h1
    · intro z hz
      have hstep : (ι a⁻¹) z ∈ Rhat := by
        show c ((ι a⁻¹) z) ∈ P₁
        have h1 : ι a⁻¹ * c z * (ι a⁻¹)⁻¹ ∈ P₁ :=
          (Subgroup.mem_normalizer_iff.mp (hιP₁ a⁻¹) (c z)).mp hz
        rw [show c ((ι a⁻¹) z) = ι a⁻¹ * c z * (ι a⁻¹)⁻¹ from (ι_conj a⁻¹ z).symm]
        exact h1
      refine ⟨(ι a⁻¹) z, hstep, ?_⟩
      show (ι a) ((ι a⁻¹) z) = z
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hιK : ∀ a : ↥A, K.map (ι a).toMonoidHom = K := by
    intro a
    have h := pCoreOf_map_mulEquiv (r := p) (e := ι a) Rhat
    rw [hιRhat a] at h
    exact h.symm
  refine ⟨K.map L.subtype, Subgroup.map_subtype_le K, hKp.map L.subtype, ?_, ?_⟩
  · intro a ha
    have hKa : K.map (ι ⟨a, ha⟩).toMonoidHom = K := hιK ⟨a, ha⟩
    have hcomp : ((MulAut.conj a).toMonoidHom.comp L.subtype) =
        (L.subtype.comp (ι ⟨a, ha⟩).toMonoidHom) := by
      ext x
      simp only [MonoidHom.comp_apply]
      exact (ι_coe ⟨a, ha⟩ x).symm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc (K.map L.subtype).map (MulAut.conj a).toMonoidHom
        = K.map ((MulAut.conj a).toMonoidHom.comp L.subtype) := Subgroup.map_map K _ _
      _ = K.map (L.subtype.comp (ι ⟨a, ha⟩).toMonoidHom) := by rw [hcomp]
      _ = (K.map (ι ⟨a, ha⟩).toMonoidHom).map L.subtype := (Subgroup.map_map K _ _).symm
      _ = K.map L.subtype := by rw [hKa]
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨ha, hc⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_bot]
    let a : ↥A := ⟨g, ha⟩
    have hιa1 : ι a = 1 := by
      have hcentP : ∀ q ∈ P, (⟨ι a, hιmemΓ a⟩ : ↥Γ) * q = q * (⟨ι a, hιmemΓ a⟩ : ↥Γ) := by
        intro q hq
        have hqP₁ : (q : MulAut ↥L) ∈ P₁ := Subgroup.mem_map_of_mem (Subgroup.subtype Γ) hq
        have hqK : (q : MulAut ↥L) ∈ K.map c := by rw [hcK]; exact hqP₁
        obtain ⟨x, hxK, hx⟩ := hqK
        have hxR : (x : G) ∈ K.map L.subtype := Subgroup.mem_map_of_mem L.subtype hxK
        have hcomm : (x : G) * g = g * (x : G) :=
          Subgroup.mem_centralizer_iff.mp hc (x : G) hxR
        have hfix : (ι a) x = x := by
          apply Subtype.ext
          rw [ι_coe]
          calc g * (x : G) * g⁻¹ = ((x : G) * g) * g⁻¹ := by rw [← hcomm]
            _ = (x : G) := by group
        have hconj : ι a * (q : MulAut ↥L) * (ι a)⁻¹ = (q : MulAut ↥L) := by
          rw [← hx, ι_conj, hfix]
        apply Subtype.ext
        show (ι a) * (q : MulAut ↥L) = (q : MulAut ↥L) * (ι a)
        calc (ι a) * (q : MulAut ↥L)
            = (ι a * (q : MulAut ↥L) * (ι a)⁻¹) * (ι a) := by group
          _ = (q : MulAut ↥L) * (ι a) := by rw [hconj]
      have hmem : (⟨ι a, hιmemΓ a⟩ : ↥Γ) ∈ P := hlieQ _ (hιNQ a) hcentP
      have hord : Nat.Coprime (orderOf (ι a)) p := by
        refine Nat.Coprime.coprime_dvd_left ?_ hAp
        exact dvd_trans (orderOf_map_dvd ι a) (orderOf_dvd_natCard a)
      obtain ⟨k, hk⟩ := hPp ⟨⟨ι a, hιmemΓ a⟩, hmem⟩
      have hk' : (⟨ι a, hιmemΓ a⟩ : ↥Γ) ^ p ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      have h1 : orderOf (⟨ι a, hιmemΓ a⟩ : ↥Γ) = 1 := by
        refine Nat.Coprime.eq_one_of_dvd ?_ (orderOf_dvd_of_pow_eq_one hk')
        rw [← Subgroup.orderOf_coe]
        exact hord.pow_right k
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
    have ha1 : a = 1 := ι_inj (hιa1.trans (map_one ι).symm)
    exact congrArg Subtype.val ha1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
