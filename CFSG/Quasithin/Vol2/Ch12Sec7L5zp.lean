module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zo
public import CFSG.LargeExtraspecial.Setting

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}

omit [Finite G] in
theorem conj_eq_of_mem_zpowers {c g : G} (hc : c ∈ Subgroup.zpowers z)
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : g * c * g⁻¹ = c := by
  rw [comm_of_mem_zpowers hc hg, mul_inv_cancel_right]

omit [Finite G] in
theorem K_le_H : K714 V z ≤ H714 T L V z := le_sup_left

section

variable (s : Set714 G T L V t z)
include s

theorem H_le_normalizer_K (h1222 : Stmt12_2_2) :
    H714 T L V z ≤ Subgroup.normalizer (K714 V z : Set G) :=
  (s.H_le_Gz h1222).trans Gz_le_normalizer_K

theorem Qz_le_Gz (h1222 : Stmt12_2_2) : s.Qz h1222 ≤ Subgroup.centralizer ({z} : Set G) :=
  fun _ hx => s.H_le_Gz h1222 hx.1

end

namespace N3

variable {s : Set714 G T L V t z} {h1222 : Stmt12_2_2} (hn : s.N3 h1222)
include hn

theorem exists_conj_mem_C0
    {a b : G} (ha : a ∈ s.Qz h1222) (hb : b ∈ s.Qz h1222) :
    ∃ h ∈ H714 T L V z, h * a * h⁻¹ ∈ V ⊓ s.Qz h1222 ⊔ U714 T L V z ∧
      h * b * h⁻¹ ∈ V ⊓ s.Qz h1222 ⊔ U714 T L V z := by
  obtain ⟨v, hv, hvz⟩ := s.exists_v h1222
  have hvU : v ∈ U714 T L V z := le_conjClosure _ _ hv
  obtain ⟨u, hu, huz, hau, hbu⟩ := hn.exists_common ha hb
  obtain ⟨h, hh, hk⟩ := hn.exists_conj hu hvU huz hvz
  set c := (h * u * h⁻¹)⁻¹ * v with hc
  have hvc : v = h * u * h⁻¹ * c := by rw [hc]; group
  have hmem : ∀ x ∈ s.Qz h1222, x * u = u * x →
      h * x * h⁻¹ ∈ V ⊓ s.Qz h1222 ⊔ U714 T L V z := by
    intro x hx hxu
    have hxQ : h * x * h⁻¹ ∈ s.Qz h1222 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_cTil _ _ hh) x).mp hx
    have hxH : h * x * h⁻¹ ∈ H714 T L V z := s.Qz_le_H h1222 hxQ
    have hcx : (h * x * h⁻¹) * c = c * (h * x * h⁻¹) :=
      comm_of_mem_zpowers hk (s.H_le_Gz h1222 hxH)
    have hxv : (h * x * h⁻¹) * v = v * (h * x * h⁻¹) := by
      rw [hvc]
      calc h * x * h⁻¹ * (h * u * h⁻¹ * c) = h * (x * u) * h⁻¹ * c := by group
        _ = h * (u * x) * h⁻¹ * c := by rw [hxu]
        _ = h * u * h⁻¹ * ((h * x * h⁻¹) * c) := by group
        _ = h * u * h⁻¹ * (c * (h * x * h⁻¹)) := by rw [hcx]
        _ = h * u * h⁻¹ * c * (h * x * h⁻¹) := by group
    have : h * x * h⁻¹ ∈ s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G) :=
      ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr hxv⟩
    rwa [hn.inf_centralizer_eq hv hvz] at this
  exact ⟨h, hh, hmem a ha hau, hmem b hb hbu⟩

theorem sq_mem {a : G}
    (ha : a ∈ s.Qz h1222) : a ^ 2 ∈ Subgroup.zpowers z := by
  obtain ⟨h, hh, ha', -⟩ := hn.exists_conj_mem_C0 ha ha
  have h2 := hn.sq_mem_C0 ha'
  have hhz := s.H_le_Gz h1222 hh
  have e : a ^ 2 = h⁻¹ * (h * a * h⁻¹) ^ 2 * h⁻¹⁻¹ := by rw [conj_pow]; group
  rw [e, conj_eq_of_mem_zpowers h2 (Subgroup.inv_mem _ hhz)]
  exact h2

theorem comm_mem {a b : G}
    (ha : a ∈ s.Qz h1222) (hb : b ∈ s.Qz h1222) : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨h, hh, ha', hb'⟩ := hn.exists_conj_mem_C0 ha hb
  have h2 := hn.comm_mem_C0 ha' hb'
  have hhz := s.H_le_Gz h1222 hh
  have e : a * b * a⁻¹ * b⁻¹ = h⁻¹ * ((h * a * h⁻¹) * (h * b * h⁻¹) * (h * a * h⁻¹)⁻¹ *
      (h * b * h⁻¹)⁻¹) * h⁻¹⁻¹ := by group
  rw [e, conj_eq_of_mem_zpowers h2 (Subgroup.inv_mem _ hhz)]
  exact h2

theorem mem_zpowers_of_comm
    {a : G} (ha : a ∈ s.Qz h1222) (hc : ∀ b ∈ s.Qz h1222, a * b = b * a) :
    a ∈ Subgroup.zpowers z := by
  by_contra haz
  have haU : a ∈ U714 T L V z := by
    rw [← hn.cent_U]
    exact ⟨s.Qz_le_H h1222 ha, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (hc u (s.U_le_Qz hn hu)).symm⟩
  exact hn.not_le_centralizer haU haz fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc b hb).symm

theorem map_rho_K :
    ((K714 V z).subgroupOf (H714 T L V z)).map (s.rho h1222) = ⊤ := by
  have hW : ∀ w : ↥(Ut T L V z), w ^ 2 = 1 := fun w =>
    Subtype.ext ((s.elemAbelian_Ut h1222).2 _ w.2)
  have : IsMulCommutative ↥(Ut T L V z) := (s.elemAbelian_Ut h1222).1
  have := G31.isSimpleGroup_mulAut hW hn.card_Ut le_rfl
  have hsurj : Function.Surjective (s.rho h1222) := by
    rw [← MonoidHom.range_eq_top, s.range_rho h1222, hn.hs_top]
  have hN : ((K714 V z).subgroupOf (H714 T L V z)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer K_le_H).mpr (s.H_le_normalizer_K h1222)
  have hNm := hN.map (s.rho h1222) hsurj
  rcases hNm.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨v, hvV, hvQ⟩ : ∃ v ∈ V, v ∉ s.Qz h1222 := by
      by_contra hno
      push Not at hno
      have hle : V ≤ V ⊓ s.Qz h1222 := fun x hx => ⟨hx, hno x hx⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [hn.card_VQ, (S127.card_eq_of_1222 h1222 s.setting.hyp).2.1] at h1
      norm_num at h1
    have hvH : v ∈ H714 T L V z := V_le_H714 T L V z hvV
    have hvK : (⟨v, hvH⟩ : ↥(H714 T L V z)) ∈ (K714 V z).subgroupOf (H714 T L V z) :=
      Subgroup.mem_subgroupOf.mpr (le_conjClosure _ _ hvV)
    have h1 : s.rho h1222 ⟨v, hvH⟩ ∈ (⊥ : Subgroup (MulAut ↥(Ut T L V z))) := by
      rw [← h]
      exact Subgroup.mem_map_of_mem _ hvK
    rw [Subgroup.mem_bot, s.mem_ker_rho h1222] at h1
    exact hvQ h1
  · exact h

theorem Qz_le_K :
    s.Qz h1222 ≤ K714 V z := by
  obtain ⟨v, hv, hvz⟩ := s.exists_v h1222
  have hvU : v ∈ U714 T L V z := le_conjClosure _ _ hv
  set KQ := K714 V z ⊓ s.Qz h1222 with hKQ
  have hUK : U714 T L V z ≤ K714 V z := conjClosure_le fun k hk x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) _).mp
      (le_conjClosure _ _ ((inf_le_left : V1 T L V ≤ V) hx))
  have hC0 : V ⊓ s.Qz h1222 ⊔ U714 T L V z ≤ KQ :=
    sup_le (fun x hx => ⟨le_conjClosure _ _ hx.1, hx.2⟩) (fun x hx => ⟨hUK hx, s.U_le_Qz hn hx⟩)
  have hKQn : ∀ h ∈ H714 T L V z, ∀ x ∈ KQ, h * x * h⁻¹ ∈ KQ := fun h hh x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp ((s.H_le_normalizer_K h1222) hh) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_cTil _ _ hh) x).mp hx.2⟩
  have hnot : ¬ KQ ≤ Subgroup.centralizer ({v} : Set G) := by
    intro hle
    have hKQU : KQ ≤ H714 T L V z ⊓ Subgroup.centralizer (U714 T L V z : Set G) := by
      intro y hy
      refine ⟨s.Qz_le_H h1222 hy.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      by_cases huz : u ∈ Subgroup.zpowers z
      · exact (comm_of_mem_zpowers huz (s.H_le_Gz h1222 (s.Qz_le_H h1222 hy.2))).symm
      · obtain ⟨h, hh, hk⟩ := hn.exists_conj hu hvU huz hvz
        set c := (h * u * h⁻¹)⁻¹ * v with hc
        have hvc : h * u * h⁻¹ = v * c⁻¹ := by rw [hc]; group
        have hy' : h * y * h⁻¹ ∈ KQ := hKQn h hh y hy
        have hyv : (h * y * h⁻¹) * v = v * (h * y * h⁻¹) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hle hy')
        have hyH : h * y * h⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
          s.H_le_Gz h1222 (s.Qz_le_H h1222 hy'.2)
        have hyc : (h * y * h⁻¹) * c⁻¹ = c⁻¹ * (h * y * h⁻¹) :=
          comm_of_mem_zpowers (Subgroup.inv_mem _ hk) hyH
        have hcomm : (h * y * h⁻¹) * (h * u * h⁻¹) = (h * u * h⁻¹) * (h * y * h⁻¹) := by
          rw [hvc]
          calc h * y * h⁻¹ * (v * c⁻¹) = (h * y * h⁻¹ * v) * c⁻¹ := by group
            _ = v * (h * y * h⁻¹ * c⁻¹) := by rw [hyv]; group
            _ = v * (c⁻¹ * (h * y * h⁻¹)) := by rw [hyc]
            _ = v * c⁻¹ * (h * y * h⁻¹) := by group
        have e : u * y = h⁻¹ * ((h * u * h⁻¹) * (h * y * h⁻¹)) * h := by group
        rw [e, ← hcomm]
        group
    rw [hn.cent_U] at hKQU
    have h1 := Subgroup.card_le_of_le (hC0.trans hKQU)
    rw [hn.card_C0, hn.card_U] at h1
    norm_num at h1
  have hlt : V ⊓ s.Qz h1222 ⊔ U714 T L V z < KQ := by
    refine lt_of_le_of_ne hC0 fun heq => hnot ?_
    rw [← heq, ← hn.inf_centralizer_eq hv hvz]
    exact inf_le_right
  have hQ : Nat.card ↥(s.Qz h1222) = 128 := by rw [hn.card_Q]; norm_num
  have h1 := Subgroup.card_dvd_of_le (inf_le_right : KQ ≤ s.Qz h1222)
  have h2 := Subgroup.card_lt_of_lt hlt
  rw [hn.card_C0] at h2
  rw [hQ] at h1
  have hKQ128 : Nat.card ↥KQ = 128 := by
    obtain ⟨k, hk⟩ := h1
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · simp at hk
        · rfl
      · nlinarith
    rw [hk1, mul_one] at hk
    exact hk.symm
  have heq : KQ = s.Qz h1222 :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hQ, hKQ128])
  exact fun x hx => (heq ▸ hx : x ∈ KQ).1

theorem K_eq_H :
    K714 V z = H714 T L V z := by
  refine le_antisymm K_le_H fun h hh => ?_
  have hm : s.rho h1222 ⟨h, hh⟩ ∈ ((K714 V z).subgroupOf (H714 T L V z)).map (s.rho h1222) := by
    rw [hn.map_rho_K]
    exact Subgroup.mem_top _
  obtain ⟨k, hk, hkh⟩ := hm
  have hker : s.rho h1222 (k⁻¹ * ⟨h, hh⟩) = 1 := by rw [map_mul, map_inv, hkh, inv_mul_cancel]
  rw [s.mem_ker_rho h1222] at hker
  have hkK : (k : G) ∈ K714 V z := Subgroup.mem_subgroupOf.mp hk
  have e : h = (k : G) * ((k⁻¹ * ⟨h, hh⟩ : ↥(H714 T L V z)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [e]
  exact (K714 V z).mul_mem hkK (hn.Qz_le_K hker)

theorem Gz_le_normalizer_H :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (H714 T L V z : Set G) := by
  rw [← hn.K_eq_H]
  exact Gz_le_normalizer_K

theorem Gz_le_normalizer_Qz :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (s.Qz h1222 : Set G) := by
  rw [← hn.pCore_H]
  exact hn.Gz_le_normalizer_H.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem centralizer_U :
    Subgroup.centralizer (U714 T L V z : Set G) = U714 T L V z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy := s.setting.hyp.hyp
  have hCN : Subgroup.centralizer (U714 T L V z : Set G) ≤
      Subgroup.normalizer (U714 T L V z : Set G) := Subgroup.centralizer_le_normalizer _
  have hNC : Subgroup.normalizer (U714 T L V z : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U714 T L V z : Set G) : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype fun x hx => S127.conj_mem_centralizer hg hx
  have hUC : U714 T L V z ≤ Subgroup.centralizer (U714 T L V z : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.mpr fun u' hu' => s.comm_U hn hu' hu
  have hU2 : IsPGroup 2 ↥(U714 T L V z) := IsPGroup.of_card (n := 4) (by rw [hn.card_U]; norm_num)
  have hTN : T ≤ Subgroup.normalizer (U714 T L V z : Set G) := (s.U_le_T h1222).2
  have hTC : T ⊓ Subgroup.centralizer (U714 T L V z : Set G) = U714 T L V z := by
    apply le_antisymm
    · intro x hx
      rw [← hn.cent_U]
      exact ⟨T_le_H hx.1, hx.2⟩
    · exact le_inf (s.U_le_T h1222).1 hUC
  have hsylT : CFSG.ABGLocalTools.IsSylowOf (G := G) 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hy.sylow.1, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hy.sylow.2
  have hsylC := (hsylT.of_le hTN le_top).inf_of_le_normalizer hCN hNC
  rw [hTC, CFSG.ABGLocalTools.isSylowOf_iff] at hsylC
  have hchar : QuasithinUnique.CharTwo (Subgroup.normalizer (U714 T L V z : Set G)) := by
    refine charTwo_of_inH hy.qtke.2.1 (hy.sylow.1.toSylow hy.sylow.2) ⟨hTN, fun hb => s.ne_one ?_⟩
    have hle : U714 T L V z ≤ pCoreOf 2 (Subgroup.normalizer (U714 T L V z : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hU2
    have := hle s.z_mem_U
    rwa [hb, Subgroup.mem_bot] at this
  exact eq_of_central_sylow hCN hNC hUC hU2
    (fun c hc u hu => (Subgroup.mem_centralizer_iff.mp hc u hu).symm) hsylC.2.2 hchar

@[expose] def zQ :
    ↥((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G))) :=
  ⟨⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, s.U_le_Qz hn s.z_mem_U⟩

theorem mem_zpowers_zQ
    {x : ↥((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G)))}
    (hx : ((x : ↥(Subgroup.centralizer ({z} : Set G))) : G) ∈ Subgroup.zpowers z) :
    x ∈ Subgroup.zpowers hn.zQ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨k, Subtype.ext (Subtype.ext (by simpa [zQ] using hk))⟩

theorem orderOf_zQ :
    orderOf hn.zQ = 2 := by
  rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  exact s.orderOf_z

theorem extraspecial :
    IsExtraspecialPGroup 2 ↥((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G))) := by
  have hcard : Nat.card ↥((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G))) =
      2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (s.Qz_le_Gz h1222)).toEquiv, hn.card_Q]
  have hmemQ : ∀ x : ↥((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G))),
      ((x : ↥(Subgroup.centralizer ({z} : Set G))) : G) ∈ s.Qz h1222 := fun x => x.2
  refine CFSG.RankThree.PartOne.PlaneCommuting.isExtraspecialPGroup_of_pairing
    (Z := Subgroup.zpowers hn.zQ) (IsPGroup.of_card hcard) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_zpowers, hn.orderOf_zQ]
  · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (g : ↥(Subgroup.centralizer ({z} : Set G))).2))
  · intro x y
    apply hn.mem_zpowers_zQ
    rw [commutatorElement_def]
    exact hn.comm_mem (hmemQ x) (hmemQ y)
  · intro x
    apply hn.mem_zpowers_zQ
    simpa using hn.sq_mem (hmemQ x)
  · intro x hx
    apply hn.mem_zpowers_zQ
    refine hn.mem_zpowers_of_comm (hmemQ x) fun b hb => ?_
    have := hx ⟨⟨b, (s.Qz_le_Gz h1222) hb⟩, hb⟩
    exact congrArg (fun y : ↥((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G))) =>
      ((y : ↥(Subgroup.centralizer ({z} : Set G))) : G)) this
  · by_contra hno
    push Not at hno
    have hle : (⊤ : Subgroup ↥((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G)))) ≤
        Subgroup.zpowers hn.zQ := fun x _ => hno x
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, hcard, Nat.card_zpowers, hn.orderOf_zQ] at this
    norm_num at this

theorem centralizer_le_Q :
    Subgroup.centralizer (((s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G)) :
      Subgroup ↥(Subgroup.centralizer ({z} : Set G))) : Set ↥(Subgroup.centralizer ({z} : Set G))) ≤
      (s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G)) := by
  intro g hg
  rw [Subgroup.mem_subgroupOf]
  have hgU : (g : G) ∈ U714 T L V z := by
    rw [← hn.centralizer_U, Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : (⟨u, (s.Qz_le_Gz h1222) (s.U_le_Qz hn hu)⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) ∈
        (s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G)) :=
      Subgroup.mem_subgroupOf.mpr (s.U_le_Qz hn hu)
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg _ hu')
  exact s.U_le_Qz hn hgU

theorem le_of_normal_Q
    (P : Subgroup ↥(Subgroup.centralizer ({z} : Set G))) (hP : P.Normal) (hP2 : IsPGroup 2 P) :
    P ≤ (s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy := s.setting.hyp.hyp
  have hTGz : T ≤ Subgroup.centralizer ({z} : Set G) := s.le_cent
  have hT2 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.centralizer ({z} : Set G))) :=
    hy.sylow.1.comap_subtype
  have hTidx : ¬ 2 ∣ (T.subgroupOf (Subgroup.centralizer ({z} : Set G))).index := fun h =>
    hy.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTGz))
  have hPS : P ≤ ((hT2.toSylow hTidx : Sylow 2 ↥(Subgroup.centralizer ({z} : Set G))) :
      Subgroup ↥(Subgroup.centralizer ({z} : Set G))) := hP2.le_sylow_of_normal _
  have hP'H : P.map (Subgroup.centralizer ({z} : Set G)).subtype ≤ H714 T L V z := by
    rintro _ ⟨x, hx, rfl⟩
    exact T_le_H (hPS hx)
  have hHP' : H714 T L V z ≤
      Subgroup.normalizer ((P.map (Subgroup.centralizer ({z} : Set G)).subtype : Subgroup G) :
        Set G) := by
    intro h hh
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have hhGz : h ∈ Subgroup.centralizer ({z} : Set G) := s.H_le_Gz h1222 hh
    exact ⟨⟨h, hhGz⟩ * y * ⟨h, hhGz⟩⁻¹, hP.conj_mem y hy _, rfl⟩
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP'H hHP'
    (hP2.map (Subgroup.centralizer ({z} : Set G)).subtype)
  rw [hn.pCore_H] at hle
  intro x hx
  exact hle ⟨x, hx, rfl⟩

@[expose] noncomputable def setting :
    CFSG.LargeExtraspecial.Setting G where
  z := z
  orderOf_z := s.orderOf_z
  Q := (s.Qz h1222).subgroupOf (Subgroup.centralizer ({z} : Set G))
  normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (s.Qz_le_Gz h1222)).mpr hn.Gz_le_normalizer_Qz
  extraspecial := hn.extraspecial
  centralizer_le := hn.centralizer_le_Q
  le_of_normal := hn.le_of_normal_Q

theorem setting_QG :
    hn.setting.QG = s.Qz h1222 := by
  show ((s.Qz h1222).subgroupOf _).map (Subgroup.centralizer ({z} : Set G)).subtype = _
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (s.Qz_le_Gz h1222)]

end N3

end CFSG.Quasithin.H13.S127.L715.Set714
