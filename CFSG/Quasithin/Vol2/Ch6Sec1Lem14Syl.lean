module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem14Fld

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_of_normalizer_le {P K H : Subgroup G} (hP : IsSylowIn 2 P K) (hKH : K ≤ H)
    (hN : H ⊓ Subgroup.normalizer (P : Set G) ≤ K) : IsSylowIn 2 P H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowIn_ge 2 (hP.le.trans hKH) hP.isPGroup
  have hNQ : Q ⊓ Subgroup.normalizer (P : Set G) ≤ P := by
    have hPX : P ≤ Q ⊓ Subgroup.normalizer (P : Set G) := le_inf hPQ Subgroup.le_normalizer
    have hXK : Q ⊓ Subgroup.normalizer (P : Set G) ≤ K := (inf_le_inf_right _ hQ.le).trans hN
    obtain ⟨k, hk⟩ := (hQ.isPGroup.to_le
      (inf_le_left : Q ⊓ Subgroup.normalizer (P : Set G) ≤ Q)).exists_card_eq
    have h1 : P.relIndex (Q ⊓ Subgroup.normalizer (P : Set G)) ∣ 2 ^ k :=
      hk ▸ Subgroup.relIndex_dvd_card _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have h2 := Subgroup.relIndex_mul_relIndex P _ K hPX hXK
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact Subgroup.relIndex_eq_one.mp hj
    · exfalso
      apply hP.not_dvd_relIndex
      rw [← h2, hj]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero j)) _
  have hnil : Group.IsNilpotent ↥Q := hQ.isPGroup.isNilpotent
  by_cases htop : P.subgroupOf Q = ⊤
  · have hQP : Q ≤ P := fun x hx => by
      have : (⟨x, hx⟩ : ↥Q) ∈ P.subgroupOf Q := htop ▸ Subgroup.mem_top _
      exact this
    rwa [le_antisymm hPQ hQP]
  exfalso
  obtain ⟨x, hxN, hxP⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.mpr htop))
  apply hxP
  show (x : G) ∈ P
  refine hNQ ⟨x.2, ?_⟩
  show (x : G) ∈ Subgroup.normalizer (P : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hx := Subgroup.mem_normalizer_iff.mp hxN
  constructor
  · intro hg
    have h1 := (hx ⟨g, hPQ hg⟩).mp hg
    exact h1
  · intro hg
    have hgQ : g ∈ Q := by
      have e : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * x := by group
      rw [e]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem x.2) (hPQ hg)) x.2
    exact (hx ⟨g, hgQ⟩).mpr hg

namespace Hyp611Nat

variable {T M L V : Subgroup G} {n : ℕ}

theorem card_le_mul_card_fix_inf_ZS (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) {A : Subgroup G} (hAS : A ≤ ch6S T L V)
    (hAU : A ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) :
    Nat.card A ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) *
      Nat.card ↥((V ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ ch6ZS T L V) := by
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set W := U ⊓ ch6ZS T L V with hW
  obtain ⟨u₀, hu₀U, hu₀Z⟩ := Set.not_subset.mp (h.not_fix_le_ZS htT ht)
  have hcommZ : ∀ a ∈ ch6ZS T L V, ∀ b ∈ ch6ZS T L V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.toHyp611.isElemAbelian (h.ZS_le ha) (h.ZS_le hb)
  have hmemW : ∀ x : ↥A, (x : G) * u₀ * (x : G)⁻¹ * u₀⁻¹ ∈ W := by
    intro x
    refine ⟨U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAU x.2) u₀).mp hu₀U) (U.inv_mem hu₀U),
      ?_⟩
    have h1 : ⁅(x : G), u₀⁆ ∈ ⁅ch6S T L V, V⁆ :=
      Subgroup.commutator_mem_commutator (hAS x.2) hu₀U.1
    rw [Subgroup.commutator_comm] at h1
    exact h.commutator_V_S_le h1
  let φ : ↥A →* ↥W :=
    { toFun := fun x => ⟨(x : G) * u₀ * (x : G)⁻¹ * u₀⁻¹, hmemW x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hb := (hmemW y).2
        have ha := (hmemW x).2
        have hxb : (x : G) * ((y : G) * u₀ * (y : G)⁻¹ * u₀⁻¹) * (x : G)⁻¹ =
            (y : G) * u₀ * (y : G)⁻¹ * u₀⁻¹ := by
          have := Subgroup.mem_centralizer_iff.mp (hAS x.2).2 _ hb
          rw [← this]
          group
        calc (x : G) * y * u₀ * ((x : G) * y)⁻¹ * u₀⁻¹ =
            ((x : G) * ((y : G) * u₀ * (y : G)⁻¹ * u₀⁻¹) * (x : G)⁻¹) *
              ((x : G) * u₀ * (x : G)⁻¹ * u₀⁻¹) := by group
          _ = ((y : G) * u₀ * (y : G)⁻¹ * u₀⁻¹) * ((x : G) * u₀ * (x : G)⁻¹ * u₀⁻¹) := by
            rw [hxb]
          _ = ((x : G) * u₀ * (x : G)⁻¹ * u₀⁻¹) * ((y : G) * u₀ * (y : G)⁻¹ * u₀⁻¹) :=
            hcommZ _ hb _ ha }
  have hcard : Nat.card A = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_le_card_of_injective (fun x =>
      ⟨((x : ↥A) : G), (x : ↥A).2, ?_⟩) ?_
    · by_contra hxV
      have hx1 : φ x = 1 := MonoidHom.mem_ker.mp x.2
      have hx2 : ((x : ↥A) : G) * u₀ * ((x : ↥A) : G)⁻¹ * u₀⁻¹ = 1 :=
        congrArg Subtype.val hx1
      have heq := h.centralizer_singleton_eq_ZS (hAS (x : ↥A).2) hxV
      apply hu₀Z
      rw [← heq]
      refine ⟨hu₀U.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      calc ((x : ↥A) : G) * u₀ = ((x : ↥A) : G) * u₀ * ((x : ↥A) : G)⁻¹ * u₀⁻¹ * (u₀ * x) := by
            group
        _ = u₀ * x := by rw [hx2, one_mul]
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card φ.range ≤ Nat.card W := Subgroup.card_le_of_le le_top |>.trans_eq
    Subgroup.card_top
  rw [hcard]
  exact Nat.mul_le_mul hker hrange

theorem thompsonJ_le_Q (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) {X : Subgroup G} (hVX : V ≤ X) (hXT : X ≤ T)
    (hXU : X ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) : thompsonJ X ≤ ch6Q T V := by
  refine GammaExtra.thompsonJ_le fun A hA => ?_
  have hAT : A ≤ T := hA.1.trans hXT
  have hV := h.toHyp611.isElemAbelian
  have hcomm : ∀ a ∈ A ⊓ Subgroup.centralizer (V : Set G), ∀ b ∈ V, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp ha.2 b hb).symm
  have hDe : IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
    B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_mono inf_le_left hA.2.1) hV hcomm
  have hDX : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ X :=
    sup_le (inf_le_left.trans hA.1) hVX
  have hDA : Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ≤ Nat.card A :=
    hA.2.2 _ hDX hDe
  have hcard0 := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊓ V) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a ha
    exact B2F.isElemAbelian_comm hA.2.1 ha hx.1.1
  have hcard : Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    calc Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) =
        Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * Nat.card V := mul_comm _ _
      _ = Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) *
          Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊓ V) := hcard0.symm
      _ ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
          Nat.mul_le_mul hDA hinf
  have hAS := h.le_S_of_card hAT hA.2.1 hcard
  refine le_inf hAT ?_
  by_contra hAV
  obtain ⟨a, haA, haV⟩ := Set.not_subset.mp hAV
  have h1 : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ 2 ^ n := by
    have hle : V ⊓ Subgroup.centralizer (A : Set G) ≤ V ⊓ Subgroup.centralizer ({a} : Set G) :=
      inf_le_inf_left V (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
    have := Subgroup.card_le_of_le hle
    rwa [h.centralizer_singleton_eq_ZS (hAS haA) haV, h.card_ZS] at this
  have h2 := h.card_le_mul_card_fix_inf_ZS htT ht hAS (hA.1.trans hXU)
  have h3 : Nat.card ↥((V ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ ch6ZS T L V) < 2 ^ n := by
    rw [← h.card_ZS]
    refine lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_right) fun heq => ?_
    apply h.not_ZS_le_fix htT ht
    have := Subgroup.eq_of_le_of_card_ge (inf_le_right :
      (V ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ ch6ZS T L V ≤ ch6ZS T L V) heq.ge
    rw [← this]
    exact inf_le_left
  have hc : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have hq : 0 < 2 ^ n := by positivity
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have key : 2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) <
      2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
    calc 2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) =
        Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by rw [hVcard]
      _ ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := hcard
      _ ≤ Nat.card A * 2 ^ n := Nat.mul_le_mul_left _ h1
      _ ≤ (Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) *
          Nat.card ↥((V ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ ch6ZS T L V)) * 2 ^ n :=
          Nat.mul_le_mul_right _ h2
      _ < (Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n) * 2 ^ n :=
          Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left h3 hc) hq
      _ = 2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring
  exact lt_irrefl _ key

theorem le_Q (h : Hyp611Nat G T M L V n) : V ≤ ch6Q T V := by
  rw [h.toHyp611.centralizer_eq]
  exact h.toHyp611.le_pCoreOf

theorem thompsonJ_eq_Q (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) {X : Subgroup G} (hQX : ch6Q T V ≤ X) (hXT : X ≤ T)
    (hXU : X ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) : thompsonJ X = thompsonJ (ch6Q T V) :=
  (GammaExtra.thompsonJ_eq_of_le (h.thompsonJ_le_Q htT ht (h.le_Q.trans hQX) hXT hXU) hQX).symm

theorem normalizer_thompsonJ_Q_le (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n) :
    Subgroup.normalizer (thompsonJ (ch6Q T V) : Set G) ≤ M := by
  have hU := h.toHyp611.isUniqueM h432
  have hQ := h.toHyp611.centralizer_eq
  have hQ2 : IsPGroup 2 (ch6Q T V) := h.sylow.1.to_le inf_le_left
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (ch6Q T V : Set G) := by
    rw [hQ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hLTJ : L ⊔ T ≤ Subgroup.normalizer (thompsonJ (ch6Q T V) : Set G) :=
    hLTQ.trans (GammaExtra.normalizer_le_normalizer_thompsonJ (ch6Q T V))
  have hJ1 : thompsonJ (ch6Q T V) ≠ ⊥ := by
    intro h0
    obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian (ch6Q T V)
    have hVA : Nat.card V ≤ Nat.card A := hA.2.2 V h.le_Q h.toHyp611.isElemAbelian
    have hA1 : A = ⊥ := eq_bot_iff.mpr (h0 ▸ GammaExtra.le_thompsonJ hA)
    rw [hA1, Subgroup.card_bot] at hVA
    exact h.toHyp611.ne_bot (Subgroup.eq_bot_of_card_le V hVA)
  exact le_of_isUniqueM_of_le_twoLocal hU hLTJ
    ⟨_, hJ1, GammaExtra.isPGroup_thompsonJ hQ2, rfl⟩

theorem lemma_6_1_14_one (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t)
    (hSyl : IsSylowIn 2 (T ⊓ Subgroup.normalizer
        ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
      (M ⊓ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G))) :
    IsSylowIn 2 (ch6Q T V ⊔ Subgroup.zpowers t)
        (Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
          Set G)) ∧
      Subgroup.normalizer (thompsonJ (ch6Q T V ⊔ Subgroup.zpowers t) : Set G) ≤ M ∧
      IsSylowIn 2 (T ⊓ Subgroup.normalizer
          ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G))
        (Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
          Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have htU : t ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp hu.2 t rfl).symm
  have hQU : ch6Q T V ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le inf_le_left)
  have hRT : R ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.mpr htT)
  have hRU : R ≤ Subgroup.centralizer (U : Set G) := sup_le hQU (Subgroup.zpowers_le.mpr htU)
  have hCN : Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCTU : T ⊓ Subgroup.centralizer (U : Set G) = R :=
    le_antisymm (h.centralizer_fix_le htT ht) (le_inf hRT hRU)
  have hNJ := h.normalizer_thompsonJ_Q_le h432
  have hJR : thompsonJ R = thompsonJ (ch6Q T V) :=
    h.thompsonJ_eq_Q htT ht le_sup_left hRT (hRU.trans hCN)
  have hQTU : ch6Q T V ≤ T ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf inf_le_left (hQU.trans hCN)
  have hJTU : thompsonJ (T ⊓ Subgroup.normalizer (U : Set G)) = thompsonJ (ch6Q T V) :=
    h.thompsonJ_eq_Q htT ht hQTU inf_le_left inf_le_right
  have hNR : Subgroup.normalizer (R : Set G) ≤ M := by
    refine (GammaExtra.normalizer_le_normalizer_thompsonJ R).trans ?_
    rw [hJR]
    exact hNJ
  refine ⟨?_, by rw [hJR]; exact hNJ, ?_⟩
  ·
    have hnorm : ((M ⊓ Subgroup.centralizer (U : Set G)).subgroupOf
        (M ⊓ Subgroup.normalizer (U : Set G))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_inf_left M hCN)]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx.1, F7.normalizer_le_normalizer_centralizer _ hx.2⟩
    have h1 := hSyl.inf_normal (inf_le_inf_left M hCN) hnorm
    have e : (T ⊓ Subgroup.normalizer (U : Set G)) ⊓ (M ⊓ Subgroup.centralizer (U : Set G)) =
        R := by
      rw [← hCTU]
      apply le_antisymm
      · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
      · exact le_inf (le_inf inf_le_left (inf_le_right.trans hCN))
          (le_inf (inf_le_left.trans h.T_le) inf_le_right)
    rw [e] at h1
    refine isSylowIn_of_normalizer_le h1 inf_le_right ?_
    exact fun x hx => ⟨hNR hx.2, hx.1⟩
  · refine isSylowIn_of_normalizer_le hSyl inf_le_right ?_
    intro x hx
    refine ⟨?_, hx.1⟩
    have h1 := GammaExtra.normalizer_le_normalizer_thompsonJ _ hx.2
    rw [hJTU] at h1
    exact hNJ h1

theorem lemma_6_1_14_two (h : Hyp611Nat G T M L V n) {t : G} (htT : t ∈ T) :
    CharTwo (Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) ∧
      CharTwo (Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
        Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  have hT : IsSylowTwoOf T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hUp : IsPGroup 2 ↥U :=
    (F7.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le inf_le_left
  have hN : CharTwo (Subgroup.normalizer (U : Set G)) := by
    refine CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hT hUp ?_
    have hne := inf_omegaOneCenter_ne_bot h.sylow.1 h.toHyp611.isElemAbelian h.toHyp611.le_T
      h.toHyp611.T_le_normalizer h.toHyp611.ne_bot
    intro h0
    apply hne
    rw [eq_bot_iff, ← h0]
    intro z hz
    have hzZ : z ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
      (Subgroup.closure_le _).mpr (fun y hy => hy.1) hz.2
    refine ⟨⟨hz.1, ?_⟩, hzZ⟩
    show z ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_centralizer_iff.mp hzZ.2 t htT
  refine ⟨hN, CharTwo.of_normal hN (Subgroup.centralizer_le_normalizer _) ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)]
  exact F7.normalizer_le_normalizer_centralizer _

theorem lemma_6_1_14_three (h6110 : Stmt6_1_10) (h : Hyp611Nat G T M L V n) {t : G}
    (htT : t ∈ T) (ht : IsInvolutoryFieldAut L t) :
    wClos V 0 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V ∧
      (2 < n → wClos V 1 (ch6Q T V ⊔ Subgroup.zpowers t) ≤ ch6Q T V) := by
  have hs : ∀ hV : IsElemAbelian 2 V, sParam hV = n := fun hV =>
    ((h6110 _ T M L V n h).2.1 hV).1
  set U := V ⊓ Subgroup.centralizer ({t} : Set G) with hU
  set R := ch6Q T V ⊔ Subgroup.zpowers t with hR
  have htU : t ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (Subgroup.mem_centralizer_iff.mp hu.2 t rfl).symm
  have hQU : ch6Q T V ≤ Subgroup.centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le inf_le_left)
  have hRT : R ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.mpr htT)
  have hRU : R ≤ Subgroup.centralizer (U : Set G) := sup_le hQU (Subgroup.zpowers_le.mpr htU)
  have hkey : ∀ i : ℕ, i + 2 ≤ n → wClos V i R ≤ ch6Q T V := by
    intro i hi
    refine wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAR, g, hAg, hm⟩ := hA
    have hAS := h.le_S_of_le_conj hs hAg (hAR.trans hRT) (by rw [hm]; exact hi)
    intro a ha
    exact ⟨hRT (hAR ha), h.mem_centralizer_of_mem_S_of_fix htT ht (hAS ha) (hRU (hAR ha))⟩
  exact ⟨hkey 0 (by have := h.two_le; omega), fun hn => hkey 1 (by omega)⟩

end Hyp611Nat

end CFSG.Quasithin.H13
