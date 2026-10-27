module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19X
public import CFSG.Quasithin.Vol2.Ch6S5Parab
public import CFSG.Quasithin.Vol2.Ch6Sec1Residuals

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace L619

theorem threePartTop_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (threePartTop A).map e.toMonoidHom = threePartTop B := by
  rw [threePartTop, threePartTop, MonoidHom.map_closure]
  congr 1
  ext b
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ⟨j, hj⟩, rfl⟩
    exact ⟨j, by rw [← map_pow, hj, map_one]⟩
  · rintro ⟨j, hj⟩
    refine ⟨e.symm b, ⟨j, ?_⟩, by simp⟩
    rw [← map_pow, hj, map_one]

theorem threePartTop_perm5 : threePartTop (Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) := by
  refine le_antisymm (threePartTop_le_alternating 5) ?_
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  refine Subgroup.closure_mono fun σ hσ => ⟨1, ?_⟩
  rw [pow_one, ← hσ.orderOf, pow_orderOf_eq_one]

theorem card_threePartTop_of_perm5 {A : Type*} [Group A] (e : A ≃* Equiv.Perm (Fin 5)) :
    Nat.card (threePartTop A) = 60 := by
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
    threePartTop_map_mulEquiv, threePartTop_perm5, nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem threePartTop_simple_of_perm5 {A : Type*} [Group A] (e : A ≃* Equiv.Perm (Fin 5))
    {N : Subgroup A} (hN : N ≤ threePartTop A)
    (hn : threePartTop A ≤ Subgroup.normalizer (N : Set A)) : N = ⊥ ∨ N = threePartTop A := by
  have hmap := threePartTop_map_mulEquiv e
  rw [threePartTop_perm5] at hmap
  let e₁ : ↥(threePartTop A) ≃* ↥(alternatingGroup (Fin 5)) :=
    (e.subgroupMap (threePartTop A)).trans (MulEquiv.subgroupCongr hmap)
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥(threePartTop A) := e₁.isSimpleGroup
  have hnorm : (N.subgroupOf (threePartTop A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (threePartTop A)) with hb | ht
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hN hx⟩ : ↥(threePartTop A)) ∈ N.subgroupOf (threePartTop A) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · right
    exact le_antisymm hN (Subgroup.subgroupOf_eq_top.mp ht)

theorem card_eq_eight_of_sylow {A : Type*} [Group A] [Finite A] (hA : Nat.card A = 120)
    {U : Subgroup A} (hU : IsSylowTwoOf U ⊤) : Nat.card U = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hU.2.1
  have hidx := hU.2.2
  rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at hidx
  have h := Subgroup.card_mul_index U
  rw [hk, hA] at h
  have hpos : 0 < U.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hk3 : k = 3 := by
    have hk7 : k < 7 := by
      by_contra hc
      push Not at hc
      have h7 : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
      have : 2 ^ 7 * 1 ≤ 2 ^ k * U.index := Nat.mul_le_mul h7 hpos
      omega
    interval_cases k <;> norm_num at h <;> omega
  rw [hk, hk3]
  norm_num

theorem threePartTop_sup_eq_top_of_perm5 {A : Type*} [Group A] [Finite A]
    (e : A ≃* Equiv.Perm (Fin 5)) {U : Subgroup A} (hU : IsSylowTwoOf U ⊤) :
    threePartTop A ⊔ U = ⊤ := by
  have hA : Nat.card A = 120 := by rw [Nat.card_congr e.toEquiv, card_perm_five]
  have h60 := card_threePartTop_of_perm5 e
  have h8 := card_eq_eight_of_sylow hA hU
  have h1 : 60 ∣ Nat.card ↥(threePartTop A ⊔ U) := h60 ▸ Subgroup.card_dvd_of_le le_sup_left
  have h2 : 8 ∣ Nat.card ↥(threePartTop A ⊔ U) := h8 ▸ Subgroup.card_dvd_of_le le_sup_right
  have h3 : Nat.card ↥(threePartTop A ⊔ U) ∣ 120 := hA ▸ Subgroup.card_subgroup_dvd_card _
  have hle := Nat.le_of_dvd (by norm_num) h3
  have hpos : 0 < Nat.card ↥(threePartTop A ⊔ U) := Nat.card_pos
  exact Subgroup.eq_top_of_card_eq _ (by rw [hA]; omega)

theorem le_ker_of_normal_two' {G : Type*} [Group G] {R : Subgroup G} {Kt : Type*} [Group Kt]
    (ψ₁ : ↥R →* Kt) (hψ : Function.Surjective ψ₁)
    (hO2 : ∀ N : Subgroup Kt, N.Normal → IsPGroup 2 N → N = ⊥) {N : Subgroup G} (hNR : N ≤ R)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N) :
    ∀ x (hx : x ∈ N), ψ₁ ⟨x, hNR hx⟩ = 1 := by
  have hnorm : (N.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mpr hRN
  have hN2' : IsPGroup 2 (N.subgroupOf R) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNR).symm
  have hb := hO2 _ (hnorm.map ψ₁ hψ) (hN2'.map ψ₁)
  intro x hx
  have : ψ₁ ⟨x, hNR hx⟩ ∈ (N.subgroupOf R).map ψ₁ := ⟨⟨x, hNR hx⟩, hx, rfl⟩
  rwa [hb, Subgroup.mem_bot] at this

theorem mem_normalizer_preimage_of_iff {G : Type} [Group G] {R : Subgroup G} {Kt : Type*}
    [Group Kt] (ψ₁ : ↥R →* Kt) {Q : Subgroup Kt} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G))
    (hiff : ∀ x : ↥R, ψ₁ (conjIn hg x) ∈ Q ↔ ψ₁ x ∈ Q) :
    g ∈ Subgroup.normalizer (((Q.comap ψ₁).map R.subtype : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨conjIn hg x, (hiff x).mpr hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    have hyR : y ∈ R := (Subgroup.mem_normalizer_iff.mp hg y).mpr (hxy ▸ x.2)
    refine ⟨⟨y, hyR⟩, ?_, rfl⟩
    have e : x = conjIn hg ⟨y, hyR⟩ := Subtype.ext hxy
    have hx' : ψ₁ x ∈ Q := hx
    rw [e] at hx'
    exact (hiff _).mp hx'

end L619

theorem false_of_s5_hStar {G : Type} [Group G] [Finite G] {S M L V : Subgroup G} {n : ℕ}
    (h' : Hyp611 G S M L V n) {Hs : Subgroup G} {Kt : Type} [Group Kt] [Finite Kt]
    (eK : Kt ≃* Equiv.Perm (Fin 5))
    (ψ : ↥Hs →* Kt) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (hSH : S ≤ Hs) (hO : pCoreOf 2 Hs ≠ ⊥) (hHM : ¬ Hs ≤ M) {Q : Subgroup Kt}
    (hover : ∀ R : Subgroup Kt, (S.subgroupOf Hs).map ψ ≤ R → R ≤ Q ∨ R = ⊤)
    (hQM : ∀ x : ↥Hs, ψ x ∈ Q → (x : G) ∈ M)
    (hlift : IsHStar S M Hs → E1.LiftS5.RootFourLift Hs S (eK.toMonoidHom.comp ψ)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSsyl : IsSylowTwoOf S Hs := h'.toHyp5_0_1.isSylowTwoOf hSH
  have hkerS : ∀ x : ↥Hs, ψ x = 1 → (x : G) ∈ S := by
    intro x hx
    have hle : ψ.ker.map Hs.subtype ≤ pCoreOf 2 Hs := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _) ?_
        (hker.map _)
      intro g hg
      refine mem_normalizer_of_forall_conj_mem_of_le fun u hu => ?_
      obtain ⟨r, hr, rfl⟩ := hu
      exact ⟨⟨g, hg⟩ * r * ⟨g, hg⟩⁻¹, (MonoidHom.normal_ker ψ).conj_mem r hr ⟨g, hg⟩, rfl⟩
    exact F7.isSylowTwoOf_pCoreOf_le hSsyl (hle ⟨x, hx, rfl⟩)
  have hHs : IsHStar S M Hs := by
    refine ⟨⟨hSH, hO⟩, hHM, fun Y hY hYH hYM => ?_⟩
    have hR : (S.subgroupOf Hs).map ψ ≤ (Y.subgroupOf Hs).map ψ :=
      Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hY.1 (Subgroup.mem_subgroupOf.mp hx))
    rcases hover _ hR with hle | htop
    · exfalso
      apply hYM
      intro y hy
      exact hQM ⟨y, hYH hy⟩ (hle ⟨⟨y, hYH hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
    · refine le_antisymm hYH fun x hx => ?_
      have hx' : ψ ⟨x, hx⟩ ∈ (Y.subgroupOf Hs).map ψ := htop ▸ Subgroup.mem_top _
      obtain ⟨w, hw, hwx⟩ := hx'
      have hk : ψ (w⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hwx, inv_mul_cancel]
      have hkS := hkerS _ hk
      have e : x = (w : G) * ((w⁻¹ * ⟨x, hx⟩ : ↥Hs) : G) := by simp
      rw [e]
      exact Y.mul_mem (Subgroup.mem_subgroupOf.mp hw) (hY.1 hkS)
  have hT : IsSylowIn 2 S Hs :=
    E6.isSylowIn_of_le ⟨le_top, h'.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h'.sylow.2⟩
      hSH le_top
  have hA5 : alternatingGroup (Fin 5) ≤ (eK.toMonoidHom.comp ψ).range := by
    rw [MonoidHom.range_eq_top.mpr (eK.surjective.comp hψ)]
    exact le_top
  have h1 := E1.LiftS5.one_lt_nParam_of_rootFourLift hA5 hT (hlift hHs)
  rw [h'.nParam_eq_one Hs hHs] at h1
  exact lt_irrefl _ h1

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace Dat619

variable {z : G} {T' D' : Subgroup G} (hd : Dat619 T M L V H n y z T' D')
include hd

theorem parabolic_of_s5 (h : Hyp6116 G T M L V n) (hT' : Hyp611 G T' M L V n)
    (h432 : Stmt4_3_2) (hres : Res619S5)
    (hW : IsElemAbelian 2 (ch619W T L V z))
    {Ks : Fin 1 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))}
    (hdec : G6.IsTransvectionDecomposition
      (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks)
    (hND : L619.NormDec hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) Ks)
    (hK : Nonempty (↥(Ks 0) ≃* Equiv.Perm (Fin 5))) :
    Parab619 T M L V T' D' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := hd.cfg
  have hz := hd.z619
  have hY := hd.isY
  revert Ks
  set I := ch619I T L V with hI
  set P := conjClosure (conjSub y V) (I ⊔ T') with hP
  set K := L619.img0 hW (ch6ZS T L V) P with hKdef
  set S' := T' ⊓ I with hS'
  set NW := L619.normWZX (ch619W T L V z) (ch6ZS T L V) P with hNW
  intro Ks hdec hND hK
  have hKorig := hK
  have hK0 : Ks 0 = K := by
    rw [← hdec.iSup_eq]
    refine le_antisymm (le_iSup Ks 0) (iSup_le fun j => ?_)
    rw [Subsingleton.elim j 0]
  rw [hK0] at hK
  obtain ⟨eK⟩ := hK
  have hcardK : Nat.card K = 120 := by rw [Nat.card_congr eK.toEquiv, L619.card_perm_five]
  have h3 : 3 ∣ Nat.card ↥K := by rw [hcardK]; norm_num
  have hZK : Subgroup.center ↥K = ⊥ := by
    have := Subgroup.map_center_eq eK
    rw [L619.center_perm5, Subgroup.map_eq_bot_iff_of_injective _ eK.injective] at this
    exact this
  have hO2K : ∀ N : Subgroup ↥K, N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hN2
    have : (N.map eK.toMonoidHom).Normal := hN.map _ eK.surjective
    have hb := L619.eq_bot_of_normal_two_perm5 (N := N.map eK.toMonoidHom) (hN2.map _)
    exact (Subgroup.map_eq_bot_iff_of_injective _ eK.injective).mp hb
  have hPN := c.conjClosure_E_le_normWZX hY
  set ψ := L619.actOn hW (ch6ZS T L V) P hPN (fun x => L619.act0_mem_img0 hW _ P x.2) with hψ
  have hψs : Function.Surjective ψ := L619.actOn_surjective hW _ P hPN
  have hψ1 : ∀ x : ↥P, ψ x = 1 ↔ (x : G) ∈ ch619K2 T L V z := by
    intro x
    rw [Subtype.ext_iff]
    exact c.act0_eq_one_iff h h432 hz hY hW (x := Subgroup.inclusion hPN x) x.2
  have hcyc : ∀ p [Fact p.Prime], p ≠ 2 → ∀ Q : Sylow p ↥K, IsCyclic Q := fun p hp hp2 Q =>
    CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd
      (by rw [hcardK]; exact L619.not_sq_dvd_of_small (Or.inr (Or.inl rfl)) hp.out hp2) Q
  have hPK2 : P ⊓ ch619K2 T L V z ≤ pCoreOf 2 P := c.inf_K2_le_pCoreOf h h432 hz hY hW hcyc
  have hker : IsPGroup 2 ψ.ker := by
    have hle : ψ.ker ≤ (pCoreOf 2 P).subgroupOf P := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hPK2 ⟨x.2, (hψ1 x).mp hx⟩)
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).symm).to_le hle
  have hPI : P ≤ I := c.conjClosure_E_le_I hY
  have hIP : I ≤ Subgroup.normalizer (P : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  have hA := L619.threeComp_of ψ ((L619.threePart_le P).trans hPI) hIP hψs hker
    (fun N hN hNn => L619.threePartTop_simple_of_perm5 eK hN hNn) (by rw [hcardK]; decide) h3
  have hO : ∀ x (hx : x ∈ P), x ∈ pCoreOf 2 I → ψ ⟨x, hx⟩ = 1 := fun x hx hxO =>
    (hψ1 ⟨x, hx⟩).mpr (Cfg619.pCoreOf_I_le_K2 h h432 z hxO)
  have hwit := L619.exists_commutator_not_mem ψ hψs hZK h3 hO
  have hP3 : ∀ x ∈ P, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ L619.threePart P :=
    fun x hx k hk => L619.mem_threePart hx hk
  have hDA : D' ≤ Subgroup.normalizer (L619.threePart P : Set G) := fun d hdD =>
    mem_normalizer_of_conjSub_le' (L619.ThreeComp.conjSub_eq_of_pRank hd.rank_I hA hPI hIP hP3
      hwit (hd.D'_le_I hdD) (hd.pow_three_eq_one hdD)).le
  have hS'P : IsSylowTwoOf (S' ⊓ P) P := A4.isSylowTwoOf_inf_normal hd.sylow_S' hPI hIP
  have hkerS : ψ.ker.map P.subtype ≤ S' ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact F7.isSylowTwoOf_pCoreOf_le hS'P (hPK2 ⟨x.2, (hψ1 x).mp hx⟩)
  have htop : L619.threePartTop ↥K ⊔ ((S' ⊓ P).subgroupOf P).map ψ = ⊤ :=
    L619.threePartTop_sup_eq_top_of_perm5 eK (L619.isSylowTwoOf_map_surj hS'P ψ hψs)
  have hPA : P ≤ L619.threePart P ⊔ (S' ⊓ P) :=
    L619.le_threePart_sup ψ hψs inf_le_right hkerS htop
  have heq : L619.threePart P ⊔ S' = P ⊔ S' :=
    le_antisymm (sup_le_sup_right (L619.threePart_le P) _)
      (sup_le (hPA.trans (sup_le_sup_left inf_le_left _)) le_sup_right)
  have hRI : P ⊔ S' ≤ I := sup_le hPI inf_le_right
  have hRN : P ⊔ S' ≤ NW := hRI.trans (hY.I_le.trans (Cfg619.Y_le_normWZX hY))
  have hTN : T' ≤ NW := fun t ht => Cfg619.Y_le_normWZX hY (Subgroup.mem_sup_right ht)
  let β : ↥NW →* ↥K :=
    (L619.act0 hW (ch6ZS T L V) P).codRestrict K fun g =>
      L619.act0_mem_img0_of_normDec hW _ P hdec hND g
  let ψ₁ : ↥(P ⊔ S') →* ↥K := β.comp (Subgroup.inclusion hRN)
  have hcomp : ∀ x : ↥P, ψ₁ (Subgroup.inclusion le_sup_left x) = ψ x := fun x => rfl
  have hψ₁s : Function.Surjective ψ₁ := fun k => by
    obtain ⟨x, rfl⟩ := hψs k
    exact ⟨_, hcomp x⟩
  have hker₁ : IsPGroup 2 ψ₁.ker :=
    L619.isPGroup_ker_sup ψ hd.sylow_S'.2.1 (inf_le_right.trans hIP) hψs hker ψ₁ hcomp
  have hS'R : IsSylowTwoOf S' (P ⊔ S') :=
    F7.isSylowTwoOf_mono_right hd.sylow_S' le_sup_right hRI
  set U : Subgroup ↥K := (S'.subgroupOf (P ⊔ S')).map ψ₁ with hU
  have hUsyl : IsSylowTwoOf U ⊤ := L619.isSylowTwoOf_map_surj hS'R ψ₁ hψ₁s
  obtain ⟨Q, hUQ, hover, ρ, hρs, hρk⟩ := L619.s5_parabolics eK hUsyl
  have hTS' : ∀ t ∈ T', t ∈ Subgroup.normalizer (S' : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hd.T'_le_I ht⟩
  have hTR : ∀ t ∈ T', t ∈ Subgroup.normalizer ((P ⊔ S' : Subgroup G) : Set G) := fun t ht =>
    L619.mem_normalizer_sup
      (le_normalizer_conjClosure _ _ (Subgroup.mem_sup_right ht : t ∈ I ⊔ T'))
      (hTS' t ht)
  have hDR : ∀ d ∈ D', d ∈ Subgroup.normalizer ((P ⊔ S' : Subgroup G) : Set G) :=
    fun d hdD => by
      rw [← heq]
      exact L619.mem_normalizer_sup (hDA hdD) (hd.D'_le_S' hdD)
  have hβconj : ∀ (g : ↥NW) (hgR : (g : G) ∈ Subgroup.normalizer ((P ⊔ S' : Subgroup G) : Set G))
      (x : ↥(P ⊔ S')), ψ₁ (L619.conjIn hgR x) = β g * ψ₁ x * (β g)⁻¹ := by
    intro g hgR x
    have e : Subgroup.inclusion hRN (L619.conjIn hgR x) =
        g * Subgroup.inclusion hRN x * g⁻¹ := Subtype.ext rfl
    show β (Subgroup.inclusion hRN (L619.conjIn hgR x)) = _
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hTU : ∀ t (ht : t ∈ T'), β ⟨t, hTN ht⟩ ∈ U := by
    have hle : U ≤ (T'.subgroupOf NW).map β := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨Subgroup.inclusion hRN s,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hs).1, rfl⟩
    have h2 : IsPGroup 2 ((T'.subgroupOf NW).map β) :=
      (hd.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm).map β
    have heqU := F1.eq_of_isSylowTwoOf_le hUsyl le_top h2 hle
    intro t ht
    rw [heqU]
    exact ⟨⟨t, hTN ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hDQ : ∀ d (hdD : d ∈ D') (x : ↥(P ⊔ S')),
      ψ₁ (L619.conjIn (hDR d hdD) x) ∈ Q ↔ ψ₁ x ∈ Q := by
    intro d hdD
    have hdR := hDR d hdD
    have hkerd : ∀ x : ↥(P ⊔ S'), ψ₁ x = 1 → ψ₁ (L619.conjIn hdR x) = 1 := by
      set N : Subgroup G := (ψ₁.ker.map (P ⊔ S').subtype).map (MulAut.conj d).toMonoidHom
        with hN
      have hNR : N ≤ P ⊔ S' := by
        rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hdR w).mp w.2
      have hRNn : P ⊔ S' ≤ Subgroup.normalizer (N : Set G) := by
        refine L619.le_normalizer_of_forall_conj fun r hr v hv => ?_
        obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hv
        have hr' : d⁻¹ * r * d ∈ P ⊔ S' := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdR) r).mp hr
          simpa using this
        let r' : ↥(P ⊔ S') := ⟨d⁻¹ * r * d, hr'⟩
        refine ⟨((r' * w * r'⁻¹ : ↥(P ⊔ S')) : G), ⟨r' * w * r'⁻¹, ?_, rfl⟩, ?_⟩
        · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
            MonoidHom.mem_ker.mp hw, mul_one, mul_inv_cancel]
        · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
            Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype, r']
          group
      have hN2 : IsPGroup 2 N := (hker₁.map (P ⊔ S').subtype).map _
      have hle := L619.le_ker_of_normal_two' ψ₁ hψ₁s hO2K hNR hRNn hN2
      intro x hx
      exact hle (d * x * d⁻¹) ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨α, hα⟩ := L619.exists_induced_aut ψ₁ hψ₁s hdR hkerd
    have hαU : ∀ u ∈ U, α u ∈ U := by
      rintro _ ⟨s, hs, rfl⟩
      rw [hα]
      exact ⟨L619.conjIn hdR s, Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hd.D'_le_S' hdD) s).mp (Subgroup.mem_subgroupOf.mp hs)),
        rfl⟩
    have hUmap : U.map α.toMonoidHom = U := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        exact hαU u hu
      · exact (Subgroup.card_map_of_injective α.injective).ge
    have hQα : Q.map α.toMonoidHom = Q := by
      have hUα : U ≤ Q.map α.toMonoidHom := by
        rw [← hUmap]
        exact Subgroup.map_mono hUQ
      rcases hover _ hUα with hle | htop'
      · exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective α.injective).ge
      · have hQt : Q = ⊤ := by
          refine Subgroup.eq_top_of_card_eq _ ?_
          rw [← Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective, htop',
            Subgroup.card_top]
        rw [htop', hQt]
    intro x
    rw [← hα]
    constructor
    · intro hx
      rw [← hQα] at hx
      obtain ⟨q, hq, hqx⟩ := hx
      rw [show q = ψ₁ x from α.injective hqx] at hq
      exact hq
    · intro hx
      rw [← hQα]
      exact ⟨_, hx, rfl⟩
  set P₁ : Subgroup G := (Q.comap ψ₁).map (P ⊔ S').subtype with hP₁
  have hP₁R : P₁ ≤ P ⊔ S' := Subgroup.map_subtype_le _
  have hS'P₁ : S' ≤ P₁ := fun s hs =>
    ⟨⟨s, Subgroup.mem_sup_right hs⟩,
      hUQ ⟨⟨s, Subgroup.mem_sup_right hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, rfl⟩
  have hTP₁ : T' ≤ Subgroup.normalizer (P₁ : Set G) := fun t ht =>
    L619.mem_normalizer_preimage ψ₁ (hTR t ht) (hUQ (hTU t ht))
      (hβconj ⟨t, hTN ht⟩ (hTR t ht))
  have hDP₁ : D' ≤ Subgroup.normalizer (P₁ : Set G) := fun d hdD =>
    L619.mem_normalizer_preimage_of_iff ψ₁ (hDR d hdD) (hDQ d hdD)
  have hP₁I : P₁ ≤ I := hP₁R.trans hRI
  refine ⟨P₁, hP₁I, hTP₁, hDP₁, ?_, ?_, ?_⟩
  ·
    intro hle
    have hT'P : T' ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
      le_normalizer_conjClosure _ _ (Subgroup.mem_sup_right ht : t ∈ I ⊔ T')
    have hHsN : P ⊔ T' ≤ NW := sup_le (hPI.trans (hY.I_le.trans (Cfg619.Y_le_normWZX hY))) hTN
    let ψH : ↥(P ⊔ T') →* ↥K := β.comp (Subgroup.inclusion hHsN)
    have hcompH : ∀ x : ↥P, ψH (Subgroup.inclusion le_sup_left x) = ψ x := fun x => rfl
    have hψHs : Function.Surjective ψH := fun k => by
      obtain ⟨x, rfl⟩ := hψs k
      exact ⟨_, hcompH x⟩
    have hkerH : IsPGroup 2 ψH.ker :=
      L619.isPGroup_ker_sup ψ hd.sylow.1 hT'P hψs hker ψH hcompH
    have hZ2 : IsPGroup 2 (ch6ZS T L V) :=
      (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le h.toHyp611Nat.ZS_le
    have hT'syl : IsSylowTwoOf T' ⊤ :=
      ⟨le_top, hd.sylow.1, by
        rw [show (T'.subgroupOf ⊤).index = T'.index from Subgroup.relIndex_top_right T']
        exact hd.sylow.2⟩
    have hZT : ch6ZS T L V ≤ T' := by
      have hsup : IsPGroup 2 ↥(ch6ZS T L V ⊔ T') := hZ2.to_sup_of_normal_left' hd.sylow.1 hd.T'_le
      have := F1.eq_of_isSylowTwoOf_le hT'syl le_top hsup le_sup_right
      rw [this]
      exact le_sup_left
    have hlift : IsHStar T' M (P ⊔ T') →
        E1.LiftS5.RootFourLift (P ⊔ T') T' (eK.toMonoidHom.comp ψH) := by
      intro hHs
      refine hres G T M L V H n y z T' D' h hT' hd hW Ks hdec hKorig hHs hHsN _
        (eK.surjective.comp hψHs) fun x => ?_
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
      exact Subtype.ext_iff
    refine false_of_s5_hStar hT' eK ψH hψHs hkerH le_sup_right ?_ ?_ (Q := Q) ?_ ?_ hlift
    · intro hb
      have hZH : ch6ZS T L V ≤ P ⊔ T' := hZT.trans le_sup_right
      have hHZ : P ⊔ T' ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
        sup_le (hPI.trans (Subgroup.centralizer_le_normalizer _)) hd.T'_le
      have hle' := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZH hHZ hZ2
      rw [hb, le_bot_iff] at hle'
      exact h.toHyp611Nat.ZS_ne_bot hle'
    · intro hHM
      exact c.not_le_M h h432 ((conjClosure_mono le_rfl hY.I_le).trans (le_sup_left.trans hHM))
    · intro R hR
      refine hover R (le_trans ?_ hR)
      rintro _ ⟨s, hs, rfl⟩
      have hsT : (s : G) ∈ T' := (Subgroup.mem_subgroupOf.mp hs).1
      exact ⟨⟨s, Subgroup.mem_sup_right hsT⟩, Subgroup.mem_subgroupOf.mpr hsT, rfl⟩
    · intro x hx
      have hx' : (x : G) ∈ ((P ⊔ T' : Subgroup G) : Set G) := x.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left P T' hT'P] at hx'
      obtain ⟨p, hp, t, ht, hpt⟩ := hx'
      have hψx : ψH x = ψ ⟨p, hp⟩ * β ⟨t, hTN ht⟩ := by
        have e : x = Subgroup.inclusion le_sup_left ⟨p, hp⟩ * ⟨t, Subgroup.mem_sup_right ht⟩ :=
          Subtype.ext hpt.symm
        rw [e, map_mul]
        rfl
      have hpQ : ψ₁ ⟨p, Subgroup.mem_sup_left hp⟩ ∈ Q := by
        have e : ψ ⟨p, hp⟩ = ψH x * (β ⟨t, hTN ht⟩)⁻¹ := by rw [hψx]; group
        show ψ ⟨p, hp⟩ ∈ Q
        rw [e]
        exact Q.mul_mem hx (Q.inv_mem (hUQ (hTU t ht)))
      have hpM : p ∈ M := hle ⟨⟨p, Subgroup.mem_sup_left hp⟩, hpQ, rfl⟩
      rw [← hpt]
      exact M.mul_mem hpM (hT'.T_le ht)
  · have heqS : T' ⊓ P₁ = S' :=
      le_antisymm (le_inf inf_le_left (inf_le_right.trans hP₁I)) (le_inf inf_le_left hS'P₁)
    rw [heqS]
    exact F7.isSylowTwoOf_mono_right hd.sylow_S' hS'P₁ hP₁I
  ·
    let ι := Subgroup.equivMapOfInjective (Q.comap ψ₁) (P ⊔ S').subtype
      (P ⊔ S').subtype_injective
    let θ : ↥P₁ →* ↥Q := (ψ₁.subgroupComap Q).comp ι.symm.toMonoidHom
    have hθs : Function.Surjective θ :=
      (MonoidHom.subgroupComap_surjective ψ₁ Q hψ₁s).comp ι.symm.surjective
    have hsk : IsPGroup 2 (ψ₁.subgroupComap Q).ker := by
      refine (hker₁.comap_of_injective (Q.comap ψ₁).subtype
        (Q.comap ψ₁).subtype_injective).to_le ?_
      intro x hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker]
      have h0 : (ψ₁.subgroupComap Q) x = 1 := hx
      exact congrArg Subtype.val h0
    have hθk : IsPGroup 2 θ.ker :=
      L619.isPGroup_ker_comp _ _ (L619.isPGroup_ker_of_injective _ ι.symm.injective) hsk
    exact nonempty_quot_perm3_of_surjective (ρ.comp θ) (hρs.comp hθs)
      (L619.isPGroup_ker_comp _ _ hθk hρk)

end Dat619

theorem case619S5_of (h432 : Stmt4_3_2) (hres : Res619S5) : Case619S5 := by
  intro G _ _ T M L V H n y z T' D' h hT' hd hW Ks hdec hND hK
  exact hd.parabolic_of_s5 h hT' h432 hres hW hdec hND hK

end CFSG.Quasithin.H13
