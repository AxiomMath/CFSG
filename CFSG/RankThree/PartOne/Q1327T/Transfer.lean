module

public import CFSG.RankThree.PartOne.Q1327T.ThetaLift
public import CFSG.RankThree.PartOne.S15K.SL2Model
public import CFSG.RankThree.PartOne.S12.Equivariance
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.Q1327T.Defs

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Torsion37
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem injective_subgroupMap_of_simple {M Q : Type*} [Group M] [Group Q] (K : Subgroup M)
    (hK : IsSimpleGroup K) (hne : ∃ a b : K, a * b ≠ b * a) (φ : M →* Q)
    (hφ : Group.IsSolvable φ.ker) : Function.Injective (φ.subgroupMap K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : (φ.subgroupMap K).ker = ⊥ ∨ (φ.subgroupMap K).ker = ⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal _
  rcases hker with h | h
  · have : x ∈ (φ.subgroupMap K).ker := hx
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · exfalso
    obtain ⟨a, b, hab⟩ := hne
    have hKle : K ≤ φ.ker := by
      intro k hk
      have : (⟨k, hk⟩ : K) ∈ (φ.subgroupMap K).ker := h ▸ Subgroup.mem_top _
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 this)
      exact MonoidHom.mem_ker.2 this
    have hsolK : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKle)
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolK a b)

variable {G : Type} [Group G] [Finite G]

theorem isElementaryAbelian_of_map {p : ℕ} (hp : p.Prime) {N : Subgroup G} {F₃ : Subgroup ↥N}
    (hF₃p : IsPGroup p F₃) {F : Subgroup (↥N ⧸ aschbacherSolvableCore p ↥N)}
    [hF : IsElementaryAbelian p F]
    (hmap : F₃.map (QuotientGroup.mk' (aschbacherSolvableCore p ↥N)) = F) :
    IsElementaryAbelian p F₃ := by
  have : Fact p.Prime := ⟨hp⟩
  set θ := aschbacherSolvableCore p ↥N with hθ
  have hinj := injOn_mk_of_isPGroup hp hF₃p
  have hmem : ∀ u ∈ F₃, QuotientGroup.mk' θ u ∈ F := fun u hu =>
    hmap ▸ Subgroup.mem_map_of_mem _ hu
  refine { toIsMulCommutative := ⟨⟨fun u v => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    refine hinj (mul_mem u.2 v.2) (mul_mem v.2 u.2) ?_
    simp only [Subgroup.coe_mul, map_mul]
    exact congrArg Subtype.val (hF.is_comm.comm ⟨_, hmem u u.2⟩ ⟨_, hmem v v.2⟩)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun u => ?_
    apply Subtype.ext
    refine hinj (pow_mem u.2 p) (one_mem F₃) ?_
    simp only [Subgroup.coe_one, map_pow, map_one]
    have h1 : (⟨_, hmem u u.2⟩ : F) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p F) _
    exact congrArg Subtype.val h1

theorem row8Conf_of_data {p g : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hg2 : 2 ≤ g)
    (hpg : p ∣ 2 ^ g + 1) {N : Subgroup G}
    (hQ : CFSG.IsQuasisimple (↥N ⧸ aschbacherSolvableCore p ↥N))
    (hList : Census3.TheoremThreeList
      ((↥N ⧸ aschbacherSolvableCore p ↥N) ⧸ Subgroup.center (↥N ⧸ aschbacherSolvableCore p ↥N)))
    {a : G} (haN : ∀ n ∈ N, a * n = n * a) (hao : a ^ p = 1) {P : Subgroup G} (hPN : P ≤ N)
    (hPel : IsElementaryAbelian p ↥P) (hPcard : Nat.card P = p ^ 2) {E : Subgroup G}
    (hE : E = Subgroup.zpowers a ⊔ P)
    (hEmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → F ≤ Subgroup.centralizer (E : Set G) →
      E ≤ F → F = E)
    {c₀ x : G} (hc₀P : c₀ ∈ P) (hc₀1 : c₀ ≠ 1) {K : Subgroup G} (hKN : K ≤ N)
    (hKc : K ≤ Subgroup.centralizer ({c₀} : Set G))
    (hKnorm : (K.subgroupOf (N ⊓ Subgroup.centralizer ({c₀} : Set G))).Normal)
    (hKmodel : StatedClassicalModel K .PSL 2 2 g) (hxK : x ∈ K) (hxP : x ∈ P)
    (hxo : orderOf x = p) (hPgen : P = Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x) :
    Row8Conf p g (↥N ⧸ aschbacherSolvableCore p ↥N)
      ((P.subgroupOf N).map (QuotientGroup.mk' (aschbacherSolvableCore p ↥N))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hPel
  set θ := aschbacherSolvableCore p ↥N with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Pn : Subgroup ↥N := P.subgroupOf N with hPn
  have hPnel : IsElementaryAbelian p ↥Pn := IsElementaryAbelian.subgroupOf hPN
  have hPnp : IsPGroup p ↥Pn := IsElementaryAbelian.isPGroup p _
  have hθsolv : Group.IsSolvable θ := (solvable_prime_complement_core_characterization hp).1
  set c₀' : ↥N := ⟨c₀, hPN hc₀P⟩ with hc₀'
  set x' : ↥N := ⟨x, hPN hxP⟩ with hx'
  have hPnsup : Pn = Subgroup.zpowers c₀' ⊔ Subgroup.zpowers x' := by
    apply Subgroup.map_injective N.subtype_injective
    rw [hPn, Subgroup.map_subgroupOf_eq_of_le hPN, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    exact hPgen
  have hdisj : Pn ⊓ θ = ⊥ := pGroup_inf_theta hp hPnp
  have hπinj : ∀ u ∈ Pn, π u = 1 → u = 1 := by
    intro u hu h
    have : u ∈ Pn ⊓ θ := ⟨hu, (QuotientGroup.eq_one_iff u).1 h⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  refine ⟨hp, hp5, hg2, hpg, hQ, isPGroup_center_quotient hp, hList, ?_, ?_, ?_, ?_⟩
  ·
    have := hPnel
    exact IsElementaryAbelian.map π
  ·
    rw [card_map_mk_of_isPGroup hp hPnp]
    rw [hPn]
    rw [← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  ·
    intro F hFel hFC hEF
    have hFp : IsPGroup p ↥F := IsElementaryAbelian.isPGroup p _
    obtain ⟨F₃, hPF₃, hF₃p, hF₃F⟩ := exists_pGroup_cover hp hPnp hFp hEF
    have hF₃el : IsElementaryAbelian p ↥F₃ := by
      have := hFel
      exact isElementaryAbelian_of_map hp hF₃p hF₃F
    set F₃G : Subgroup G := F₃.map N.subtype with hF₃G
    have hF₃Gel : IsElementaryAbelian p ↥F₃G := by
      have := hF₃el
      exact IsElementaryAbelian.map_subtype
    have haz : IsElementaryAbelian p ↥(Subgroup.zpowers a) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hao
    have hCE : Subgroup.zpowers a ≤ Subgroup.centralizer (F₃G : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      rintro z ⟨f, -, rfl⟩
      exact (haN _ f.2).symm
    have hFt : IsElementaryAbelian p ↥(F₃G ⊔ Subgroup.zpowers a : Subgroup G) := by
      have := hF₃Gel
      have := haz
      exact IsElementaryAbelian.sup_of_le_centralizer hCE
    have hPF₃G : P ≤ F₃G := fun y hy => ⟨⟨y, hPN hy⟩, hPF₃ (Subgroup.mem_subgroupOf.2 hy), rfl⟩
    have hEF' : E ≤ F₃G ⊔ Subgroup.zpowers a := by
      rw [hE]
      exact sup_le le_sup_right (hPF₃G.trans le_sup_left)
    have hFC' : F₃G ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer (E : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact congrArg Subtype.val (hFt.is_comm.comm ⟨e, hEF' he⟩ ⟨z, hz⟩)
    have hFE := hEmax _ hFt hFC' hEF'
    have hF₃GE : F₃G ≤ E := hFE ▸ le_sup_left
    intro y hy
    rw [← hF₃F] at hy
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hy
    have hfE : (f : G) ∈ E := hF₃GE ⟨f, hf, rfl⟩
    rw [hE] at hfE
    obtain ⟨s, hs, u, hu, hfsu⟩ := exists_mul_of_mem_sup_of_commute
      (K := Subgroup.zpowers a) (L := P) (fun k hk l hl => by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        exact ((Commute.zpow_left (haN l (hPN hl)) m)).eq) hfE
    have hsN : s ∈ N := by
      have : s = (f : G) * u⁻¹ := by rw [hfsu]; group
      rw [this]
      exact mul_mem f.2 (inv_mem (hPN hu))
    set s' : ↥N := ⟨s, hsN⟩ with hs'
    set u' : ↥N := ⟨u, hPN hu⟩ with hu'
    have hfsu' : f = s' * u' := Subtype.ext hfsu
    have hsc : ∀ n ∈ N, s * n = n * s := fun n hn => by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hs
      rw [← hm]
      exact (Commute.zpow_left (haN n hn) m).eq
    have hscen : π s' ∈ Subgroup.center (↥N ⧸ θ) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
      show π n * π s' = π s' * π n
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hsc n n.2).symm
    have hcomm : π s' * π u' = π u' * π s' := (Subgroup.mem_center_iff.1 hscen (π u')).symm
    have hfe : π f = π u' * π s' := by rw [hfsu', map_mul, hcomm]
    rw [hfe]
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hu)) hscen
  ·
    have hc₀Pn : c₀' ∈ Pn := Subgroup.mem_subgroupOf.2 hc₀P
    have hx'Pn : x' ∈ Pn := Subgroup.mem_subgroupOf.2 hxP
    set K' : Subgroup ↥N := K.subgroupOf N with hK'
    have hKq := S15K.isQuasisimple_of_model hKmodel
    have hKc0 := S15K.center_eq_bot_of_model hKmodel
    let eKc : ↥K ≃* (↥K ⧸ Subgroup.center ↥K) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hKc0.symm)
    have hKsimple : IsSimpleGroup ↥K := by
      have h1 : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2.1
      exact eKc.isSimpleGroup
    have hK'simple : IsSimpleGroup ↥K' := by
      have := hKsimple
      exact (Subgroup.subgroupOfEquivOfLe hKN).isSimpleGroup
    have hKne : ∃ a b : ↥K, a * b ≠ b * a := by
      obtain ⟨u, v, huv⟩ := hKq.2.2
      refine ⟨eKc.symm u, eKc.symm v, fun h => huv ?_⟩
      have := congrArg eKc h
      simpa using this
    have hK'ne : ∃ a b : ↥K', a * b ≠ b * a := by
      obtain ⟨u, v, huv⟩ := hKne
      refine ⟨(Subgroup.subgroupOfEquivOfLe hKN).symm u, (Subgroup.subgroupOfEquivOfLe hKN).symm v,
        fun h => huv ?_⟩
      have := congrArg (Subgroup.subgroupOfEquivOfLe hKN) h
      simpa using this
    have hinjK : Function.Injective (π.subgroupMap K') :=
      injective_subgroupMap_of_simple K' hK'simple hK'ne π (by
        rw [hπ, QuotientGroup.ker_mk']
        exact hθsolv)
    let eKK : ↥K' ≃* ↥(K'.map π) :=
      MulEquiv.ofBijective (π.subgroupMap K') ⟨hinjK, π.subgroupMap_surjective K'⟩
    have hKmodel' : StatedClassicalModel ↥(K'.map π) .PSL 2 2 g :=
      Equivariance.statedClassicalModel_of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe hKN).symm.trans eKK) hKmodel
    refine ⟨π c₀', Subgroup.mem_map_of_mem _ hc₀Pn, ?_, K'.map π, π x', ?_, ?_, hKmodel',
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxK), ?_, ?_⟩
    · intro h1
      exact hc₀1 (congrArg (fun z : ↥N => (z : G)) (hπinj c₀' hc₀Pn h1))
    ·
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.1 (hKc (Subgroup.mem_subgroupOf.1 hk)))
    ·
      have hc₀p : c₀' ^ p = 1 := by
        have h0 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := P) c₀ hc₀P
        exact Subtype.ext h0
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨k', hk', hkn⟩ := Subgroup.mem_map.1 hn
      obtain ⟨m0, hm0⟩ := QuotientGroup.mk_surjective (g : ↥N ⧸ θ)
      have hgc : π c₀' * (g : ↥N ⧸ θ) = (g : ↥N ⧸ θ) * π c₀' :=
        (Subgroup.mem_centralizer_singleton_iff.1 g.2).symm
      obtain ⟨m, hmπ, hmc⟩ := exists_commute_lift hp hc₀p (n := m0) (by
        rw [hm0]
        exact hgc)
      have hmN : (m : G) ∈ N ⊓ Subgroup.centralizer ({c₀} : Set G) := by
        refine ⟨m.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        exact congrArg (fun z : ↥N => (z : G)) hmc.symm
      have hk'N : (k' : G) ∈ N ⊓ Subgroup.centralizer ({c₀} : Set G) :=
        ⟨k'.2, hKc (Subgroup.mem_subgroupOf.1 hk')⟩
      have hconj := hKnorm.conj_mem ⟨(k' : G), hk'N⟩
        (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hk')) ⟨(m : G), hmN⟩
      have hconjK : (m : G) * (k' : G) * (m : G)⁻¹ ∈ K := Subgroup.mem_subgroupOf.1 hconj
      have hmem : m * k' * m⁻¹ ∈ K' := Subgroup.mem_subgroupOf.2 hconjK
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m * k' * m⁻¹, hmem, ?_⟩)
      have hmg : π m = (g : ↥N ⧸ θ) := hmπ.trans hm0
      rw [map_mul, map_mul, map_inv, hmg, hkn]
      rfl
    ·
      have hx'p : x' ^ p = 1 := Subtype.ext (by
        have := pow_orderOf_eq_one x
        rwa [hxo] at this)
      have hx1 : x' ≠ 1 := fun h => by
        have : x = 1 := congrArg (fun z : ↥N => (z : G)) h
        rw [this, orderOf_one] at hxo
        exact hp.ne_one hxo.symm
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, hx'p, map_one]
      · intro h
        exact hx1 (hπinj x' hx'Pn h)
    ·
      rw [hPnsup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]

end CFSG.RankThree.PartOne.Q1327T
