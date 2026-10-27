module

public import CFSG.Quasithin.Background.B53FFJImage
public import CFSG.Quasithin.Background.C124B2102
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DI
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5EFF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

abbrev UX615 (T L H : Subgroup G) : Subgroup G :=
  conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H)

namespace Cx615C

theorem U_red_ch615 (c : Cx615C G T M L V H n) :
    UX615 T L H ≤ pCoreOf 2 (borelL T L ⊔ H) ∧ IsElemAbelian 2 (UX615 T L H) ∧
      IsTwoReducedIn (borelL T L ⊔ H) (UX615 T L H) := by
  have h := c.hyp
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hsyl : IsSylowTwoOf T (borelL T L ⊔ H) := h.toHyp5_0_1.isSylowTwoOf hTX
  have hchar : CharTwo (borelL T L ⊔ H) := charTwo_of_inH' h.qtke h.sylow ⟨hTX, c.X_O2⟩
  obtain ⟨hle, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hchar le_rfl
  exact ⟨hle.trans inf_le_left, hel, hred⟩

theorem b53Hyp_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H)) :
    B53Hyp (ffJ (autI hU (borelL T L ⊔ H))) := by
  have h := c.hyp
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  obtain ⟨hk, hq⟩ := isSQTKSub_of_inH h.qtke h.simple h.nonabelian ⟨hTX, c.X_O2⟩
  have hS : SQTKGroup ↥(borelL T L ⊔ H) := ⟨hq, hk⟩
  have hO2 : pCoreOf 2 (convHom hU (borelL T L ⊔ H) hXN).range = ⊥ := by
    rw [range_convHom]
    exact C124.pCoreOf_autI_eq_bot hU c.U_red_ch615.2.2
  have := FFJImage.b53Hyp_ffJ_range hS (convHom hU (borelL T L ⊔ H) hXN) hO2
  rwa [range_convHom] at this

end Cx615C

noncomputable abbrev preI615 {T L H : Subgroup G} (hU : IsElemAbelian 2 (UX615 T L H))
    (B : Subgroup (MulAut (IntMod (UX615 T L H) hU))) : Subgroup G :=
  (B.comap (convI hU)).map (Subgroup.normalizer (UX615 T L H : Set G)).subtype

omit [Finite G] in
theorem autI_le_of_le_preI615 {T L H : Subgroup G} {hU : IsElemAbelian 2 (UX615 T L H)}
    {B : Subgroup (MulAut (IntMod (UX615 T L H) hU))} {A : Subgroup G} (hA : A ≤ preI615 hU B) :
    autI hU A ≤ B := by
  intro φ hφ
  obtain ⟨g, hgA, rfl⟩ := (mem_autI hU).mp hφ
  obtain ⟨y, hy, hyg⟩ := hA hgA
  have hyg' : y = g := Subtype.ext hyg
  rw [← hyg']
  exact hy

omit [Finite G] in
theorem mem_preI615 {T L H : Subgroup G} {hU : IsElemAbelian 2 (UX615 T L H)}
    {B : Subgroup (MulAut (IntMod (UX615 T L H) hU))} {g : G}
    (hg : g ∈ Subgroup.normalizer (UX615 T L H : Set G)) (h : convI hU ⟨g, hg⟩ ∈ B) :
    g ∈ preI615 hU B :=
  ⟨⟨g, hg⟩, h, rfl⟩

namespace Cx615C

theorem le_ffJ_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H)) :
    autI hU (thompsonJ T) ≤ ffJ (autI hU (borelL T L ⊔ H)) ∧
      autI hU (oTwoUpper H) ≤ ffJ (autI hU (borelL T L ⊔ H)) := by
  set X := borelL T L ⊔ H with hXdef
  set Gs := ffJ (autI hU X) with hGs
  have hTX : T ≤ X := c.hH.1.1.trans le_sup_right
  have hXN : X ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_normalizer_conjClosure _ _
  have hUT : UX615 T L H ≤ T :=
    c.U_red_ch615.1.trans (F7.isSylowTwoOf_pCoreOf_le (c.hyp.toHyp5_0_1.isSylowTwoOf hTX))
  have hJ : thompsonJ T ≤ preI615 hU Gs := by
    refine iSup₂_le fun A hA => fun a ha => ?_
    have haN : a ∈ Subgroup.normalizer (UX615 T L H : Set G) := hXN (hTX (hA.1 ha))
    refine mem_preI615 haN ?_
    by_cases hAC : A ≤ Subgroup.centralizer (UX615 T L H : Set G)
    · rw [(convI_eq_one_iff hU _).mpr (hAC ha)]
      exact Gs.one_mem
    · have hoff := offenderImages_isFFStarOffender hU hUT (hTX.trans hXN) ⟨A, ⟨hA, hAC⟩, rfl⟩
      have hoff' : IsFFStarOffender (autI hU X) (autI hU A) :=
        ⟨hoff.1.trans (autI_mono hU hTX), hoff.2.1, hoff.2.2.1, hoff.2.2.2⟩
      exact B6.le_ffJ hoff' (convI_mem_autI hU ha haN)
  refine ⟨autI_le_of_le_preI615 hJ, autI_le_of_le_preI615 ?_⟩
  rw [← c.JK, Subgroup.commutator_le]
  intro k hk j hj
  have hkN : k ∈ Subgroup.normalizer (UX615 T L H : Set G) :=
    hXN (Subgroup.mem_sup_right (oTwoUpper_le H hk))
  have hjN : j ∈ Subgroup.normalizer (UX615 T L H : Set G) :=
    hXN (hTX (thompsonJ_le_self T hj))
  obtain ⟨y, hy, hyj⟩ := hJ hj
  have hyj' : y = ⟨j, hjN⟩ := Subtype.ext hyj
  rw [hyj'] at hy
  have hkX : convI hU ⟨k, hkN⟩ ∈ autI hU X :=
    convI_mem_autI hU (Subgroup.mem_sup_right (oTwoUpper_le H hk)) hkN
  have hcN : ⁅k, j⁆ ∈ Subgroup.normalizer (UX615 T L H : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN hjN) (Subgroup.inv_mem _ hkN))
      (Subgroup.inv_mem _ hjN)
  refine mem_preI615 hcN ?_
  have e : (⟨⁅k, j⁆, hcN⟩ : ↥(Subgroup.normalizer (UX615 T L H : Set G))) =
      ⟨k, hkN⟩ * ⟨j, hjN⟩ * (⟨k, hkN⟩)⁻¹ * (⟨j, hjN⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact Gs.mul_mem ((Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ _ hkX) _).mp hy)
    (Gs.inv_mem hy)

theorem autI_oTwoUpper_ne_bot_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) : autI hU (oTwoUpper H) ≠ ⊥ := by
  obtain ⟨k, hkK, -, hkC⟩ := c.exists_odd_ch615
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hkN := hXN (Subgroup.mem_sup_right (oTwoUpper_le H hkK))
  intro hb
  have hk1 := convI_mem_autI hU hkK hkN
  rw [hb, Subgroup.mem_bot, convI_eq_one_iff] at hk1
  exact hkC (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
    (conjClosure_mono le_rfl le_sup_right : Cx615.UH T H ≤ UX615 T L H)) hk1)

end Cx615C

theorem borelL_le_normalizer_of_autI_ch615 {T L H : Subgroup G}
    (hU : IsElemAbelian 2 (UX615 T L H))
    (h : ∀ y ∈ autI hU (borelL T L), ∀ k ∈ autI hU (oTwoUpper H),
      y * k * y⁻¹ ∈ autI hU (oTwoUpper H)) :
    borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) := by
  set K := oTwoUpper H with hKdef
  set C := cXU615 T L H with hCdef
  set X := borelL T L ⊔ H with hXdef
  have hXN : X ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_normalizer_conjClosure _ _
  have hKX : K ≤ X := (oTwoUpper_le H).trans le_sup_right
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := hKX.trans le_normalizer_cXU615
  have hKCeq := Subgroup.coe_mul_of_left_le_normalizer_right K C hKC
  intro b hb
  have hbX : b ∈ X := Subgroup.mem_sup_left hb
  have hbC : b ∈ Subgroup.normalizer (C : Set G) := le_normalizer_cXU615 hbX
  have hbU : b ∈ Subgroup.normalizer (UX615 T L H : Set G) := hXN hbX
  apply mem_normalizer_of_conj_mem_ch6
  intro x hx
  have hx' : x ∈ ((K ⊔ C : Subgroup G) : Set G) := hx
  rw [hKCeq] at hx'
  obtain ⟨k, hk, c', hc', rfl⟩ := hx'
  have hkU : k ∈ Subgroup.normalizer (UX615 T L H : Set G) := hXN (hKX hk)
  have hmem := h _ (convI_mem_autI hU hb hbU) _ (convI_mem_autI hU hk hkU)
  obtain ⟨k', hk'K, hk'eq⟩ := (mem_autI hU).mp hmem
  have hbkb : b * k * b⁻¹ ∈ X := X.mul_mem (X.mul_mem hbX (hKX hk)) (X.inv_mem hbX)
  have hbkbN : b * k * b⁻¹ ∈ Subgroup.normalizer (UX615 T L H : Set G) := hXN hbkb
  have hcen : (k' : G)⁻¹ * (b * k * b⁻¹) ∈ C := by
    refine ⟨X.mul_mem (X.inv_mem (hKX hk'K)) hbkb, ?_⟩
    have e : (⟨(k' : G)⁻¹ * (b * k * b⁻¹), Subgroup.mul_mem _ (Subgroup.inv_mem _ k'.2) hbkbN⟩ :
        ↥(Subgroup.normalizer (UX615 T L H : Set G))) =
        k'⁻¹ * (⟨b, hbU⟩ * ⟨k, hkU⟩ * (⟨b, hbU⟩)⁻¹) := rfl
    have h1 : convI hU (k'⁻¹ * (⟨b, hbU⟩ * ⟨k, hkU⟩ * (⟨b, hbU⟩)⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hk'eq, inv_mul_cancel]
    rw [← e] at h1
    exact (convI_eq_one_iff hU _).mp h1
  have e : b * (k * c') * b⁻¹ = (k' : G) * ((k' : G)⁻¹ * (b * k * b⁻¹)) * (b * c' * b⁻¹) := by
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hk'K)
    (Subgroup.mem_sup_right hcen))
    (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hbC c').mp hc'))

theorem sign_eq_one_iff_ch615 :
    ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 ↔ σ ^ 3 = 1 := by decide

theorem mem_alternatingGroup_iff_ch615 (σ : Equiv.Perm (Fin 3)) :
    σ ∈ alternatingGroup (Fin 3) ↔ σ ^ 3 = 1 := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_eq_one_iff_ch615]

theorem pow_six_perm3_ch615 : ∀ σ : Equiv.Perm (Fin 3), σ ^ 6 = 1 := by decide

theorem card_alternatingGroup_three_ch615 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

namespace Cx615C

theorem not_b56Case2_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)) :
    ¬ B56Case2 (ffJ (autI hU (borelL T L ⊔ H))) := by
  rintro ⟨⟨e⟩, -⟩
  apply hN
  set X := borelL T L ⊔ H with hXdef
  set Gs := ffJ (autI hU X) with hGs
  have hXN : X ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_normalizer_conjClosure _ _
  set A3 : Subgroup (MulAut (IntMod (UX615 T L H) hU)) :=
    ((alternatingGroup (Fin 3)).map e.symm.toMonoidHom).map Gs.subtype with hA3
  have hA3G : A3 ≤ Gs := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hA3iff : ∀ g (hg : g ∈ Gs), g ∈ A3 ↔ g ^ 3 = 1 := by
    intro g hg
    constructor
    · rintro ⟨x, ⟨σ, hσ, rfl⟩, rfl⟩
      have hσ3 := (mem_alternatingGroup_iff_ch615 σ).mp hσ
      have : (e.symm σ) ^ 3 = 1 := by rw [← map_pow]; simp [hσ3]
      simpa using congrArg Subtype.val this
    · intro h3
      have hg3 : (⟨g, hg⟩ : ↥Gs) ^ 3 = 1 := Subtype.ext (by simpa using h3)
      refine ⟨⟨g, hg⟩, ⟨e ⟨g, hg⟩, ?_, by simp⟩, rfl⟩
      show e ⟨g, hg⟩ ∈ alternatingGroup (Fin 3)
      rw [mem_alternatingGroup_iff_ch615, ← map_pow, hg3, map_one]
  have hodd3 : ∀ g ∈ Gs, Odd (orderOf g) → g ^ 3 = 1 := by
    intro g hg hodd
    have h6 : (⟨g, hg⟩ : ↥Gs) ^ 6 = 1 := e.injective (by rw [map_pow, pow_six_perm3_ch615, map_one])
    have h6' : g ^ 6 = 1 := by simpa using congrArg Subtype.val h6
    have hd : orderOf g ∣ 2 * 3 := orderOf_dvd_of_pow_eq_one h6'
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left hd)
  have hKG := (c.le_ffJ_ch615 hU).2
  have hKA : autI hU (oTwoUpper H) ≤ A3 := by
    apply autI_le_of_le_preI615
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, hxodd⟩
    have hxN : x ∈ Subgroup.normalizer (UX615 T L H : Set G) := hXN (Subgroup.mem_sup_right hxH)
    refine mem_preI615 hxN ?_
    have hxG := hKG (convI_mem_autI hU (mem_oTwoUpper_of_odd hxH hxodd) hxN)
    refine (hA3iff _ hxG).mpr (hodd3 _ hxG ?_)
    have := orderOf_map_dvd (convI hU) ⟨x, hxN⟩
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hxodd this
  have hA3card : Nat.card A3 = 3 := by
    rw [hA3, Subgroup.card_map_of_injective Gs.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, card_alternatingGroup_three_ch615]
  have hKeq : autI hU (oTwoUpper H) = A3 := by
    have hdvd : Nat.card (autI hU (oTwoUpper H)) ∣ 3 := hA3card ▸ Subgroup.card_dvd_of_le hKA
    have hne : Nat.card (autI hU (oTwoUpper H)) ≠ 1 := fun h1 =>
      c.autI_oTwoUpper_ne_bot_ch615 hU (Subgroup.eq_bot_of_card_eq _ h1)
    have h3 : Nat.card (autI hU (oTwoUpper H)) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hKA (by rw [h3, hA3card])
  refine borelL_le_normalizer_of_autI_ch615 hU fun y hy k hk => ?_
  rw [hKeq] at hk ⊢
  have hyX : y ∈ autI hU X := autI_mono hU le_sup_left hy
  have hkG : k ∈ Gs := hA3G hk
  have hykG : y * k * y⁻¹ ∈ Gs :=
    (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ _ hyX) k).mp hkG
  refine (hA3iff _ hykG).mpr ?_
  rw [conj_pow, (hA3iff k hkG).mp hk, mul_one, mul_inv_cancel]

end Cx615C

theorem res615EFF_of_cases (hB56 : AsB56)
    (hcases : ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ),
      Cx615C G T M L V H n → ∀ hU : IsElemAbelian 2 (UX615 T L H),
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) →
      (B56Case1 (ffJ (autI hU (borelL T L ⊔ H))) ∨ B56Case3 (ffJ (autI hU (borelL T L ⊔ H))) ∨
        B56Case4 (ffJ (autI hU (borelL T L ⊔ H))) ∨
        B56Case5 (ffJ (autI hU (borelL T L ⊔ H)))) →
      ∃ z ∈ quasithinOmegaOneCenter T ⊓ ⁅UX615 T L H, borelL T L ⊔ H⁆,
        z ≠ 1 ∧ (∃ d ∈ borelL T L, Odd (orderOf d) ∧ d ≠ 1 ∧ d * z * d⁻¹ = z) ∧
        ¬ (borelL T L ⊔ H) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer ((borelL T L : Subgroup G) : Set G)) :
    Res615EFF := by
  intro G _ _ T M L V H n c hN
  obtain ⟨-, hU, -⟩ := c.U_red_ch615
  have hne : ffJ (autI hU (borelL T L ⊔ H)) ≠ ⊥ := by
    intro hb
    have hK := (c.le_ffJ_ch615 hU).2
    rw [hb] at hK
    exact c.autI_oTwoUpper_ne_bot_ch615 hU (le_bot_iff.mp hK)
  rcases hB56 (IntMod (UX615 T L H) hU) IntMod.sq_eq_one _ hne (c.b53Hyp_ch615 hU) with
    h1 | h2 | h3 | h4 | h5
  · exact hcases G T M L V H n c hU hN (Or.inl h1)
  · exact absurd h2 (c.not_b56Case2_ch615 hU hN)
  · exact hcases G T M L V H n c hU hN (Or.inr (Or.inl h3))
  · exact hcases G T M L V H n c hU hN (Or.inr (Or.inr (Or.inl h4)))
  · exact hcases G T M L V H n c hU hN (Or.inr (Or.inr (Or.inr h5)))

end CFSG.Quasithin.H13
