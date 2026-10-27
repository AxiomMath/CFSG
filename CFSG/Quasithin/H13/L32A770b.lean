module

public import CFSG.Quasithin.H13.L32A770a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem comm_mem_of_relIndex_two {A B : Subgroup G} (hidx : A.relIndex B = 2) {t : G}
    (htB : t ∈ Subgroup.normalizer (B : Set G)) (htA : t ∈ Subgroup.normalizer (A : Set G))
    {b : G} (hb : b ∈ B) : t * b * t⁻¹ * b⁻¹ ∈ A := by
  have htb : t * b * t⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp htB b).mp hb
  have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t * b * t⁻¹, htb⟩)
    (b := (⟨b, hb⟩ : ↥B)⁻¹)).mpr
  have h1 : (⟨t * b * t⁻¹, htb⟩ : ↥B) ∈ A.subgroupOf B ↔ ((⟨b, hb⟩ : ↥B)⁻¹) ∈ A.subgroupOf B := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_inv, inv_mem_iff]
    exact (Subgroup.mem_normalizer_iff.mp htA b).symm
  have h2 := key h1
  rw [Subgroup.mem_subgroupOf] at h2
  simpa using h2

omit [Finite G] in
theorem relIndex_eq_two_of_card {A B : Subgroup G} (hAB : A ≤ B) (hA : Nat.card ↥A = 2)
    (hB : Nat.card ↥B = 4) : A.relIndex B = 2 := by
  have := Subgroup.relIndex_mul_card A B
  rw [inf_eq_left.mpr hAB, hA, hB] at this
  omega

theorem conjSub_eq_of_le {X : Subgroup G} {t : G} (hle : conjSub t X ≤ X) : conjSub t X = X :=
  Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])

theorem sl24_transitive' : ∀ v w : Fin 2 → RuType.F4, v ≠ 0 → w ≠ 0 →
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) RuType.F4,
      (A : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec v = w := by
  decide +kernel

theorem eq_fsuU_of_lt (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {X : Subgroup G} (hVX : u0 T V ≤ X) (hXU : X ≤ fsuU T V)
    (hXK : kz T V ≤ Subgroup.normalizer (X : Set G)) (hne : X ≠ u0 T V) : X = fsuU T V := by
  obtain ⟨-, π, β, hπs, -, -, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  have hβ1 : ∀ u : ↥(fsuU T V), β u = 1 ↔ (u : G) ∈ u0 T V := fun u => by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  obtain ⟨w, hwX, hwV⟩ : ∃ w ∈ X, w ∉ u0 T V := by
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hc hVX)
  have hwU := hXU hwX
  have hβw : Multiplicative.toAdd (β ⟨w, hwU⟩) ≠ 0 := fun h0 => hwV ((hβ1 _).mp (by
    rw [← ofAdd_toAdd (β ⟨w, hwU⟩), h0]; rfl))
  refine le_antisymm hXU fun u hu => ?_
  by_cases hβu : Multiplicative.toAdd (β ⟨u, hu⟩) = 0
  · exact hVX ((hβ1 _).mp (by rw [← ofAdd_toAdd (β ⟨u, hu⟩), hβu]; rfl))
  obtain ⟨A, hA⟩ := sl24_transitive' _ _ hβw hβu
  obtain ⟨k, rfl⟩ := hπs A
  have hkw : (k : G) * w * (k : G)⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_U h hMod ((oTwoUpper_le (hz T V)) k.2))
      w).mp hwU
  have h1 := hβe k ⟨w, hwU⟩ ⟨_, hkw⟩ rfl
  rw [hA, ofAdd_toAdd] at h1
  have h2 : β (⟨u, hu⟩ * (⟨_, hkw⟩ : ↥(fsuU T V))⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := (hβ1 _).mp h2
  have hkwX : (k : G) * w * (k : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXK k.2) w).mp hwX
  have h3' : u * ((k : G) * w * (k : G)⁻¹)⁻¹ ∈ u0 T V := by simpa using h3
  rw [show u = (u * ((k : G) * w * (k : G)⁻¹)⁻¹) * ((k : G) * w * (k : G)⁻¹) by group]
  exact mul_mem (hVX h3') hkwX

theorem mem_u0_of_comm (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h13322 : Stmt13_3_2_two)
    (h13314 : A6.Stmt13_3_14) (h4 : Nat.card ↥(u0 T V) = 4) {u : G} (hu : u ∈ fsuU T V)
    (hc : ∀ q ∈ pCoreOf 2 (hz T V), q * u = u * q) : u ∈ u0 T V := by
  by_contra huU0
  have hV1U0 := fsuV1_le_u0 h hMod
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  set C := fsuU T V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) with hC
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hKC : kz T V ≤ Subgroup.normalizer (C : Set G) := by
    intro k hk
    have hkH := hKH hk
    rw [← conjSub_eq_self_iff, hC, conjSub_inf, ← conjSub_centralizer,
      conjSub_eq_self_iff.mpr (hz_le_normalizer_U h hMod hkH),
      conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hkH)]
  have hKU0 : kz T V ≤ Subgroup.normalizer (u0 T V : Set G) :=
    hKH.trans (hz_le_normalizer_u0 h hMod)
  have huC : u ∈ C := ⟨hu, Subgroup.mem_centralizer_iff.mpr fun q hq => hc q hq⟩
  have hV1C : fsuV1 T V ≤ C := le_inf (hV1U0.trans hU0U) fun z hz =>
    Subgroup.mem_centralizer_iff.mpr fun q hq => (Subgroup.mem_centralizer_iff.mp
      (pCoreOf_le 2 _ hq) z hz).symm
  have hsup : C ⊔ u0 T V = fsuU T V := by
    refine eq_fsuU_of_lt h hMod h63 le_sup_right (sup_le inf_le_left hU0U) ?_ fun e => ?_
    · intro k hk
      rw [← conjSub_eq_self_iff, conjSub_sup, conjSub_eq_self_iff.mpr (hKC hk),
        conjSub_eq_self_iff.mpr (hKU0 hk)]
    · exact huU0 (e ▸ Subgroup.mem_sup_left huC)
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have h41 := lemma14_7_4_one h h13322 hMod h13314 hV2
  rw [show A6.g1 T V = hz T V from normalizer_eq_centralizer_of_card_eq_two hF.card_V₁] at h41
  have hU0C : ¬ u0 T V ≤ C := by
    intro hle
    have hUC : fsuU T V ≤ C := by rw [← hsup]; exact sup_le le_rfl hle
    have hb : ⁅V₂, pCoreOf 2 (hz T V)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv q hq
      have hvC := hUC (hV2.2.1.trans (le_conjClosure V _) hv)
      rw [Subgroup.mem_bot, commutatorElement_def,
        ← Subgroup.mem_centralizer_iff.mp hvC.2 q hq, mul_inv_cancel_right, mul_inv_cancel]
    rw [h41] at hb
    have := hF.card_V₁
    rw [hb, Subgroup.card_bot] at this
    omega
  have hidx := relIndex_eq_two_of_card hV1U0 hF.card_V₁ h4
  have hinf : C ⊓ u0 T V = fsuV1 T V := by
    refine le_antisymm (fun x hx => ?_) (le_inf hV1C hV1U0)
    by_contra hxV
    apply hU0C
    intro y hy
    have hxy := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx.2⟩) (b := ⟨y, hy⟩)
    by_cases hyV : y ∈ fsuV1 T V
    · exact hV1C hyV
    · have h1 : ((⟨x, hx.2⟩ : ↥(u0 T V)) * ⟨y, hy⟩) ∈ (fsuV1 T V).subgroupOf (u0 T V) := by
        rw [hxy, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact ⟨fun h' => absurd h' hxV, fun h' => absurd h' hyV⟩
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : y = x⁻¹ * (x * y) := by group
      rw [h2]
      exact mul_mem (inv_mem hx.1) (hV1C h1)
  have hind := (h63 G T L V h).2.2.2.2.2.1
  rcases hind C (u0 T V) hV1C hV1U0 inf_le_left hU0U hKC hKU0 hinf hsup with e | e
  · exact huU0 (hV1U0 (e ▸ huC))
  · have := hF.card_V₁
    rw [← e, h4] at this
    omega

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem mul_left (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {l : G} (hlL : l ∈ L)
    (hlH : l ∈ hz T V) :
    Not1471 T L V (hz T V) γ γ' g
      (⟨l, Subgroup.mem_sup_left (Subgroup.mem_sup_left hlL)⟩ * k) where
  setup := N.setup
  pos := N.pos
  le := N.le
  mem := mul_mem hlH N.mem
  geo := by
    obtain ⟨γ₂, hγ₂, hd, hk⟩ := N.geo
    refine ⟨γ₂, hγ₂, hd, ?_⟩
    rw [mul_smul, hk]
    exact smul_eq_of_mem_stab (by
      rw [stab_γ₀ hF.amalgamHypV.le₁]
      exact Subgroup.mem_sup_left hlL)

theorem exists_choice (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h68 : Lemma14_7_68) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ∃ l ∈ L, l ∈ hz T V ∧ conjSub (l * ((k : G) * g)) (fsuV1 T V) ≤ V₂ ⊔ u0 T V := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨s, hsW, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hZF := N.zα_le h hMod h63 hF h1222 h1332 h1334 h2
  have hFU := N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hsW hsQ
  have hZ : conjSub ((k : G) * g) (fsuV1 T V) ≤ V ⊔ u0 T V :=
    hZF.trans (le_sup_left.trans hFU.le)
  have hZU0 := N.zα_not_le_u0 hF h68 h
  obtain ⟨z, hzV1, hz1, hgen⟩ := exists_gen_of_card_two hF.card_V₁
  set x : G := (k : G) * g with hx
  have hz' : x * z * x⁻¹ ∈ V ⊔ u0 T V := hZ (mul_mem_conjSub hzV1)
  have hz'U0 : x * z * x⁻¹ ∉ u0 T V := by
    intro hm
    apply hZU0
    intro y hy
    rw [mem_conjSub] at hy
    rcases hgen _ hy with e | e
    · rw [show y = x * (x⁻¹ * y * x) * x⁻¹ by group, e]
      simp
    · rw [show y = x * (x⁻¹ * y * x) * x⁻¹ by group, e]
      exact hm
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hVN : V ≤ Subgroup.normalizer (u0 T V : Set G) :=
    (hVU.trans hUH).trans (hz_le_normalizer_u0 h hMod)
  have hz'' := hz'
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN] at hz''
  obtain ⟨v, hv, u, hu, hvu⟩ := hz''
  have hvV1 : v ∉ fsuV1 T V := fun hv1 => hz'U0 (by
    rw [← hvu]
    exact mul_mem (fsuV1_le_u0 h hMod hv1) hu)
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hzV1).1
  obtain ⟨a, haV2, haV1⟩ : ∃ a ∈ V₂, a ∉ fsuV1 T V := by
    by_contra hc
    push Not at hc
    have hle : V₂ ≤ fsuV1 T V := fun y hy => hc y hy
    have := Subgroup.card_le_of_le hle
    rw [hV2.2.2.2, hF.card_V₁] at this
    omega
  have hv1 : v ≠ 1 := fun e => hvV1 (e ▸ one_mem _)
  have ha1 : a ≠ 1 := fun e => haV1 (e ▸ one_mem _)
  have hzv : z ≠ v := fun e => hvV1 (e ▸ hzV1)
  have hza : z ≠ a := fun e => haV1 (e ▸ hzV1)
  obtain ⟨l, hlL, hlz, hlv⟩ := exists_conj_eq_pair (h.hyp1281One h13322 hMod) hzV hv hzV
    (hV2.2.1 haV2) hz1 hv1 hz1 ha1 hzv hza
  have hlH : l ∈ hz T V := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hgen y hy with rfl | rfl
    · group
    · calc y * l = l * y * l⁻¹ * l := by rw [hlz]
        _ = l * y := by group
  refine ⟨l, hlL, hlH, fun y hy => ?_⟩
  rw [mem_conjSub] at hy
  rcases hgen _ hy with e | e
  · rw [show y = (l * x) * ((l * x)⁻¹ * y * (l * x)) * (l * x)⁻¹ by group, e]
    simp
  · rw [show y = (l * x) * ((l * x)⁻¹ * y * (l * x)) * (l * x)⁻¹ by group, e]
    have e2 : l * x * z * (l * x)⁻¹ = (l * v * l⁻¹) * (l * u * l⁻¹) := by
      rw [show l * x * z * (l * x)⁻¹ = l * (x * z * x⁻¹) * l⁻¹ by group, ← hvu]
      group
    rw [e2, hlv]
    exact Subgroup.mul_mem_sup haV2
      ((Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_u0 h hMod hlH) u).mp hu)

end Not1471

end CFSG.Quasithin.H13.L32A
