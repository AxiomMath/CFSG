module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2D
public import CFSG.Quasithin.Vol2.Ch12Sec6T2Perf
public import CFSG.Quasithin.Vol2.Ch12Sec6T2Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126P S126T2
  CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace S126T2

variable {G : Type} [Group G]

theorem isSylowTwoOf_of_le_of_le {S A B : Subgroup G}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S A) (hSB : S ≤ B) (hBA : B ≤ A) :
    CFSG.QuasithinUnique.IsSylowTwoOf S B := by
  refine ⟨hSB, hS.2.1, fun h => hS.2.2 ?_⟩
  change 2 ∣ S.relIndex A
  rw [← Subgroup.relIndex_mul_relIndex S B A hSB hBA]
  exact Dvd.dvd.mul_right h _

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) :
      Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem relIndex_ne_zero_of_finite [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.index_ne_zero_of_finite

end S126T2

theorem lemma12_6_4_5_of (h1222 : Stmt12_2_2) : Lemma12_6_4_5 := by
  intro G _ _ T L V _ F v Kv S hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hH, hv, hβ, -, -, -, hLvK, hKeq, -, -, hS, hTvS, hSN⟩ := hC
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  set H := (L ⊔ T) ⊓ Gv v with hHdef
  set P := pCoreOf 2 (Kv ⊔ S) with hPdef
  set X := Lv L v ⊔ P with hXdef
  set Y := pCoreOf 2 X with hYdef
  have hR : Rsec L Kv S v = centralizerSection S X Y := rfl
  have hKG : Kv ≤ Gv v := by
    rw [hKeq]
    exact (Subgroup.closure_le _).2 fun x hx => perfectCore_le _ hx.1
  have hKSG : Kv ⊔ S ≤ Gv v := sup_le hKG hS.1
  have hS2 : IsPGroup 2 S := hS.2.1
  have hSKS := isSylowTwoOf_of_le_of_le hS (le_sup_right : S ≤ Kv ⊔ S) hKSG
  have hP2 : IsPGroup 2 P := pCoreOf_isPGroup 2 _
  have hKSP : Kv ⊔ S ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 _
  have hPS : P ≤ S := hSKS.le_of_normalizes (pCoreOf_le 2 _) hKSP hP2
  have hLvP : Lv L v ≤ Subgroup.normalizer (P : Set G) := (hLvK.trans le_sup_left).trans hKSP
  have hSP : S ≤ Subgroup.normalizer (P : Set G) := le_sup_right.trans hKSP
  have hLvperf : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
  have hHN : H ≤ Subgroup.normalizer (Lv L v : Set G) := by
    refine le_trans ?_ (normalizer_le_normalizer_perfectCore (L ⊓ Gv v))
    refine (le_inf ((inf_le_left : H ≤ L ⊔ T).trans (sup_le Subgroup.le_normalizer hTL)) ?_).trans
      Subgroup.inf_normalizer_le_normalizer_inf
    exact (inf_le_right : H ≤ Gv v).trans Subgroup.le_normalizer
  have hTvH : Tv T v ≤ H := inf_le_inf_right _ le_sup_right
  have hLvH : Lv L v ≤ H := le_inf ((Lv_le_L L v).trans le_sup_left) (Lv_le_Gv L v)
  have hd : (Tv T v).relIndex T = 4 := relIndex_Tv h1222 F hH hv hβ
  have hc : (Tv T v).relIndex S ≤ (Tv T v).relIndex T := by
    have hcardS : Nat.card S ≤ Nat.card T := by
      have hT := isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow (le_top : T ≤ ⊤)
      rw [hT.card_eq]
      exact CFSG.QuasithinUnique.card_le_twoPart le_top hS2
    have e1 := Subgroup.relIndex_mul_card (Tv T v) S
    have e2 := Subgroup.relIndex_mul_card (Tv T v) T
    rw [inf_eq_left.2 hTvS] at e1
    have hTvT : Tv T v ≤ T := inf_le_left
    rw [inf_eq_left.2 hTvT] at e2
    have hpos : 0 < Nat.card (Tv T v) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [e1, e2]
    exact hcardS
  have hS4 : (Tv T v).relIndex S ≤ 4 := hd ▸ hc
  have hP4 : (P ⊓ Subgroup.normalizer (Lv L v : Set G)).relIndex P ≤ 4 := by
    have h1 : P ⊓ Tv T v ≤ P ⊓ Subgroup.normalizer (Lv L v : Set G) :=
      inf_le_inf_left _ (hTvH.trans hHN)
    calc (P ⊓ Subgroup.normalizer (Lv L v : Set G)).relIndex P ≤ (P ⊓ Tv T v).relIndex P :=
          Subgroup.relIndex_le_of_le_left h1 (relIndex_ne_zero_of_finite _ _)
      _ = (Tv T v).relIndex P := Subgroup.inf_relIndex_left _ _
      _ ≤ (Tv T v).relIndex S := Subgroup.relIndex_le_of_le_right hPS
          (relIndex_ne_zero_of_finite _ _)
      _ ≤ 4 := hS4
  have hPN : P ≤ Subgroup.normalizer (Lv L v : Set G) :=
    le_normalizer_of_relIndex_le_four hLvperf hLvP hP2 hP4
  have hXinf : perfectCore X = Lv L v := perfectCore_sup_eq hLvperf hPN hP2
  have hNX : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Lv L v : Set G) := by
    rw [← hXinf]
    exact normalizer_le_normalizer_perfectCore X
  have hXN : X ≤ Subgroup.normalizer (Lv L v : Set G) := sup_le Subgroup.le_normalizer hPN
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := sup_le hLvP Subgroup.le_normalizer
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_pCoreOf 2 X
  have hPY : P ≤ Y := le_pCoreOf_of_le_normalizer 2 le_sup_right hXP hP2
  have hOLvY : pCoreOf 2 (Lv L v) ≤ Y :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      (hXN.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hLvY : Lv L v ⊓ Y ≤ pCoreOf 2 (Lv L v) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => (le_inf Subgroup.le_normalizer (le_sup_left.trans hXY) hl).elim
        fun h1 h2 => Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩)
      ((pCoreOf_isPGroup 2 X).to_le inf_le_right)
  have hNXP : ∀ g, g ∈ Subgroup.normalizer (Lv L v : Set G) → g ∈ Subgroup.normalizer (P : Set G) →
      g ∈ Subgroup.normalizer (X : Set G) := fun g h1 h2 => mem_normalizer_sup h1 h2
  have hNXY : ∀ g, g ∈ Subgroup.normalizer (X : Set G) → g ∈ Subgroup.normalizer (Y : Set G) :=
    fun g hg => normalizer_le_normalizer_pCoreOf 2 X hg
  have hRN : centralizerSection S X Y ≤ Subgroup.normalizer (Lv L v : Set G) :=
    (centralizerSection_le_normalizer_left S X Y).trans hNX
  have hcomm : ∀ s ∈ S, s ∈ Subgroup.normalizer (Lv L v : Set G) →
      (∀ x ∈ X, x * s * x⁻¹ * s⁻¹ ∈ Y) → ∀ l ∈ Lv L v, l * s * l⁻¹ * s⁻¹ ∈ pCoreOf 2 (Lv L v) := by
    intro s _ hsN hsY l hl
    refine hLvY ⟨?_, hsY l (le_sup_left (b := P) hl)⟩
    have h1 : s * l⁻¹ * s⁻¹ ∈ Lv L v :=
      (Subgroup.mem_normalizer_iff.1 hsN _).1 ((Lv L v).inv_mem hl)
    have e : l * s * l⁻¹ * s⁻¹ = l * (s * l⁻¹ * s⁻¹) := by group
    rw [e]
    exact (Lv L v).mul_mem hl h1
  have hsec : ∀ s ∈ S, s ∈ Subgroup.normalizer (Lv L v : Set G) →
      (∀ l ∈ Lv L v, l * s * l⁻¹ * s⁻¹ ∈ pCoreOf 2 (Lv L v)) → s ∈ centralizerSection S X Y := by
    intro s hs hsN hsl
    have hsP : s ∈ Subgroup.normalizer (P : Set G) := hSP hs
    have hsX := hNXP s hsN hsP
    refine ⟨hs, hsX, hNXY s hsX, fun x hx => ?_⟩
    have hx' : x ∈ ((Lv L v ⊔ P : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (Lv L v) P hPN] at hx'
    obtain ⟨l, hl, p, hp, rfl⟩ := hx'
    have h1 : p * s * p⁻¹ * s⁻¹ ∈ P := by
      have h2 : s * p⁻¹ * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hsP _).1 (P.inv_mem hp)
      have e : p * s * p⁻¹ * s⁻¹ = p * (s * p⁻¹ * s⁻¹) := by group
      rw [e]
      exact P.mul_mem hp h2
    have h3 : l * (p * s * p⁻¹ * s⁻¹) * l⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.1 (hLvP hl) _).1 h1
    have e : l * p * s * (l * p)⁻¹ * s⁻¹ =
        (l * (p * s * p⁻¹ * s⁻¹) * l⁻¹) * (l * s * l⁻¹ * s⁻¹) := by group
    rw [e]
    exact Y.mul_mem (hPY h3) (hOLvY (hsl l hl))
  have hReq : centralizerSection S X Y = centralizerSection S (Lv L v) (pCoreOf 2 (Lv L v)) := by
    ext s
    constructor
    · intro hs
      exact ⟨hs.1, hRN hs, normalizer_le_normalizer_pCoreOf 2 _ (hRN hs),
        hcomm s hs.1 (hRN hs) hs.2.2.2⟩
    · intro hs
      exact hsec s hs.1 hs.2.1 hs.2.2.2
  have hRvTv : Rv T L v ≤ Tv T v :=
    (isSylowTwoOf_Tv h1222 F hH hv hβ).le_of_normalizes (pCoreOf_le 2 _)
      (le_normalizer_pCoreOf 2 _) (pCoreOf_isPGroup 2 _)
  have hRvR : Rv T L v ≤ centralizerSection S X Y := by
    intro r hr
    have hrH : r ∈ H := pCoreOf_le 2 _ hr
    refine hsec r (hTvS (hRvTv hr)) (hHN hrH) fun l hl => ?_
    have hLvRv : Lv L v ⊓ Rv T L v ≤ pCoreOf 2 (Lv L v) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun l' hl' => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hl', le_normalizer_pCoreOf 2 H (hLvH hl')⟩)
        ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    refine hLvRv ⟨?_, ?_⟩
    · have h1 : r * l⁻¹ * r⁻¹ ∈ Lv L v :=
        (Subgroup.mem_normalizer_iff.1 (hHN hrH) _).1 ((Lv L v).inv_mem hl)
      have e : l * r * l⁻¹ * r⁻¹ = l * (r * l⁻¹ * r⁻¹) := by group
      rw [e]
      exact (Lv L v).mul_mem hl h1
    · have h1 : l * r * l⁻¹ ∈ Rv T L v :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H (hLvH hl)) _).1 hr
      exact (Rv T L v).mul_mem h1 ((Rv T L v).inv_mem hr)
  have hRTv : centralizerSection S X Y ⊓ Tv T v ≤ Rv T L v := by
    set D := centralizerSection H (Lv L v) (pCoreOf 2 (Lv L v)) with hD
    have hDH : D ≤ H := centralizerSection_le_left _ _ _
    have hHD : H ≤ Subgroup.normalizer (D : Set G) := fun h hh =>
      A4.mem_normalizer_of_conj_mem fun d hd => conj_mem_centralizerSection
        (Subgroup.le_normalizer hh) (hHN hh) (normalizer_le_normalizer_pCoreOf 2 _ (hHN hh)) hd
    have hDRv : D ≤ Rv T L v := le_pCoreOf_of_le_normalizer 2 hDH hHD
      (isPGroup_D h1222 F hH hv hβ)
    rintro s ⟨hsR, hsTv⟩
    rw [hReq] at hsR
    exact hDRv ⟨hTvH hsTv, hsR.2.1, hsR.2.2.1, hsR.2.2.2⟩
  have hb : Rv T L v = centralizerSection S X Y ⊓ Tv T v :=
    le_antisymm (le_inf hRvR hRvTv) hRTv
  have ha : CFSG.QuasithinUnique.IsSylowTwoOf (centralizerSection S X Y)
      (centralizerSection (Kv ⊔ S) X Y) := by
    set C := centralizerSection (Kv ⊔ S) X Y with hCdef
    set M₀ := (Kv ⊔ S) ⊓ Subgroup.normalizer (Lv L v : Set G) with hM₀
    have hCM : C ≤ M₀ := le_inf (centralizerSection_le_left _ _ _)
      ((centralizerSection_le_normalizer_left _ _ _).trans hNX)
    have hMC : M₀ ≤ Subgroup.normalizer (C : Set G) := by
      intro m hm
      have hmX := hNXP m hm.2 (hKSP hm.1)
      exact A4.mem_normalizer_of_conj_mem fun c hc =>
        conj_mem_centralizerSection (Subgroup.le_normalizer hm.1) hmX (hNXY m hmX) hc
    have hSM : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ Subgroup.normalizer (Lv L v : Set G)) M₀ :=
      isSylowTwoOf_of_le_of_le hSN (inf_le_inf_right _ le_sup_right) (inf_le_inf_right _ hKSG)
    have h1 := A4.isSylowTwoOf_inf_normal hSM hCM hMC
    have e : S ⊓ Subgroup.normalizer (Lv L v : Set G) ⊓ C = centralizerSection S X Y := by
      ext s
      constructor
      · rintro ⟨⟨hs, -⟩, hc⟩
        exact ⟨hs, hc.2⟩
      · intro hs
        exact ⟨⟨hs.1, hRN hs⟩, ⟨le_sup_right (a := Kv) hs.1, hs.2⟩⟩
    rwa [e] at h1
  have hf : P ≤ centralizerSection S X Y := by
    intro p hp
    refine ⟨hPS hp, Subgroup.le_normalizer (le_sup_right (a := Lv L v) hp),
      hXY (le_sup_right (a := Lv L v) hp), fun x hx => ?_⟩
    have h1 : x * p * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hXP hx) _).1 hp
    exact hPY (P.mul_mem h1 (P.inv_mem hp))
  have he : (Rv T L v).relIndex (centralizerSection S X Y) ≤ 4 := by
    rw [hb]
    calc (centralizerSection S X Y ⊓ Tv T v).relIndex (centralizerSection S X Y)
        = (Tv T v).relIndex (centralizerSection S X Y) := Subgroup.inf_relIndex_left _ _
      _ ≤ (Tv T v).relIndex S := Subgroup.relIndex_le_of_le_right
          (centralizerSection_le_left _ _ _) (relIndex_ne_zero_of_finite _ _)
      _ ≤ 4 := hS4
  have hh : ⁅Lv L v, centralizerSection S X Y⁆ ≤ pCoreOf 2 (Lv L v) := by
    rw [Subgroup.commutator_le]
    intro l hl r hr
    rw [commutatorElement_def]
    exact hcomm r hr.1 (hRN hr) hr.2.2.2 l hl
  rw [hR]
  exact ⟨ha, hb, hc, hd, he, hf, hRN, hh, hReq⟩

end CFSG.Quasithin.H13
