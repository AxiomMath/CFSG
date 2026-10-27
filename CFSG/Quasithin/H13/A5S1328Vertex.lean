module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A5S1327zc
public import CFSG.Quasithin.H13.A5S1328Sym4

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped commutatorElement

section VxGeneric

variable {G : Type} [Group G]

@[expose] def vxConj (x : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj x).toMonoidHom

theorem mem_vxConj {x y : G} {H : Subgroup G} : y ∈ vxConj x H ↔ x⁻¹ * y * x ∈ H := by
  unfold vxConj
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have e : x⁻¹ * ((MulAut.conj x).toMonoidHom h) * x = h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hh
  · intro hy
    refine ⟨x⁻¹ * y * x, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem vxConj_one (H : Subgroup G) : vxConj 1 H = H := by
  ext y
  rw [mem_vxConj]
  simp

theorem vxConj_vxConj (x y : G) (H : Subgroup G) :
    vxConj x (vxConj y H) = vxConj (x * y) H := by
  ext z
  rw [mem_vxConj, mem_vxConj, mem_vxConj]
  have e : (x * y)⁻¹ * z * (x * y) = y⁻¹ * (x⁻¹ * z * x) * y := by group
  rw [e]

theorem vxConj_mono {x : G} {H K : Subgroup G} (h : H ≤ K) : vxConj x H ≤ vxConj x K :=
  Subgroup.map_mono h

theorem vxConj_sup (x : G) (H K : Subgroup G) : vxConj x (H ⊔ K) = vxConj x H ⊔ vxConj x K :=
  Subgroup.map_sup H K _

theorem vxConj_le {x : G} {H K : Subgroup G} (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hHK : H ≤ K) : vxConj x H ≤ K := by
  intro y hy
  rw [mem_vxConj] at hy
  have h1 := (Subgroup.mem_normalizer_iff.mp hx _).mp (hHK hy)
  have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
  rw [e] at h1
  exact h1

theorem mem_normalizer_of_vxConj_le {x : G} {H : Subgroup G} (h1 : vxConj x H ≤ H)
    (h2 : vxConj x⁻¹ H ≤ H) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : x * h * x⁻¹ ∈ vxConj x H := by
      rw [mem_vxConj]
      have e : x⁻¹ * (x * h * x⁻¹) * x = h := by group
      rw [e]
      exact hh
    exact h1 hmem
  · intro hh
    have hmem : h ∈ vxConj x⁻¹ H := by
      rw [mem_vxConj, inv_inv]
      exact hh
    exact h2 hmem

theorem le_normalizer_of_forall {X H : Subgroup G}
    (h : ∀ l ∈ X, ∀ z ∈ H, l * z * l⁻¹ ∈ H) : X ≤ Subgroup.normalizer (H : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact h l hl z hz
  · intro hz
    have h2 := h l⁻¹ (X.inv_mem hl) _ hz
    have e : l⁻¹ * (l * z * l⁻¹) * l⁻¹⁻¹ = z := by group
    rw [e] at h2
    exact h2

theorem le_normalizer_inf {X A B : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro l hl
  have hA' := Subgroup.mem_normalizer_iff.mp (hA hl)
  have hB' := Subgroup.mem_normalizer_iff.mp (hB hl)
  rw [Subgroup.mem_normalizer_iff]
  intro z
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA' z, hB' z]

theorem commute_of_inf_eq_bot {L N1 N2 : Subgroup G} (h1 : N1 ≤ L) (h2 : N2 ≤ L)
    (hN1 : L ≤ Subgroup.normalizer (N1 : Set G)) (hN2 : L ≤ Subgroup.normalizer (N2 : Set G))
    (hinf : N1 ⊓ N2 = ⊥) {a b : G} (ha : a ∈ N1) (hb : b ∈ N2) : a * b = b * a := by
  have hab : a * b * a⁻¹ ∈ N2 := (Subgroup.mem_normalizer_iff.mp (hN2 (h1 ha)) b).mp hb
  have hba : b * a⁻¹ * b⁻¹ ∈ N1 :=
    (Subgroup.mem_normalizer_iff.mp (hN1 (h2 hb)) a⁻¹).mp (N1.inv_mem ha)
  have hc : a * b * a⁻¹ * b⁻¹ ∈ N1 ⊓ N2 := by
    refine ⟨?_, ?_⟩
    · have h3 := N1.mul_mem ha hba
      have e : a * (b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by group
      rw [e] at h3
      exact h3
    · exact N2.mul_mem hab (N2.inv_mem hb)
  rw [hinf, Subgroup.mem_bot] at hc
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hc, one_mul]

theorem irr_vxConj {L H : Subgroup G}
    (hH : ∀ J : Subgroup G, J ≤ H → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = H)
    {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) (J : Subgroup G)
    (hJ : J ≤ vxConj x H) (hJL : L ≤ Subgroup.normalizer (J : Set G)) :
    J = ⊥ ∨ J = vxConj x H := by
  have hJ' : vxConj x⁻¹ J ≤ H := by
    intro y hy
    rw [mem_vxConj, inv_inv] at hy
    have h2 := hJ hy
    rw [mem_vxConj] at h2
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [e] at h2
    exact h2
  have hJ'L : L ≤ Subgroup.normalizer ((vxConj x⁻¹ J : Subgroup G) : Set G) := by
    apply le_normalizer_of_forall
    intro l hl z hz
    rw [mem_vxConj, inv_inv] at hz
    rw [mem_vxConj, inv_inv]
    have hl' : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hx l).mp hl
    have e : x * (l * z * l⁻¹) * x⁻¹ = (x * l * x⁻¹) * (x * z * x⁻¹) * (x * l * x⁻¹)⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hJL hl') (x * z * x⁻¹)).mp hz
  have hJe : J = vxConj x (vxConj x⁻¹ J) := by
    rw [vxConj_vxConj, mul_inv_cancel, vxConj_one]
  rcases hH (vxConj x⁻¹ J) hJ' hJ'L with h | h
  · left
    calc J = vxConj x (vxConj x⁻¹ J) := hJe
      _ = vxConj x ⊥ := by rw [h]
      _ = ⊥ := by
        unfold vxConj
        exact Subgroup.map_bot _
  · right
    calc J = vxConj x (vxConj x⁻¹ J) := hJe
      _ = vxConj x H := by rw [h]

theorem card_vxConj {H : Subgroup G} [Finite G] (x : G) : Nat.card ↥(vxConj x H) = Nat.card ↥H := by
  unfold vxConj
  exact Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom) (MulEquiv.injective _)

theorem T_le_normalizer_borelOf_gen {T B : Subgroup G}
    (hTB : T ≤ Subgroup.normalizer (B : Set G)) :
    T ≤ Subgroup.normalizer (borelOf B T : Set G) := by
  intro t ht
  have htL : t ∈ Subgroup.normalizer (B : Set G) := hTB ht
  have htTL : t ∈ Subgroup.normalizer ((T ⊓ B : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp htL x).mp hxL⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htL x).mpr hxL⟩
      have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      rw [e]
      exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
  have htN : t ∈ Subgroup.normalizer
      (Subgroup.normalizer ((T ⊓ B : Subgroup G) : Set G) : Set G) :=
    Subgroup.le_normalizer htTL
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxL, hxN⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp htL x).mp hxL,
      (Subgroup.mem_normalizer_iff.mp htN x).mp hxN⟩
  · rintro ⟨hxL, hxN⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp htL x).mpr hxL,
      (Subgroup.mem_normalizer_iff.mp htN x).mpr hxN⟩

end VxGeneric

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem vx_irr_eq_bot_or_eq (S : Setting G T L V) (J : Subgroup G) (hJV : J ≤ V)
    (hJL : L ≤ Subgroup.normalizer (J : Set G)) : J = ⊥ ∨ J = V := by
  rcases S.irr.2.2.2.2.2.1 J (by rw [S.V_inf_centralizer_L]; exact bot_le) hJV hJL with h | h
  · left
    rwa [S.V_inf_centralizer_L] at h
  · exact Or.inr h

theorem vx_irr_conj (S : Setting G T L V) {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (J : Subgroup G) (hJ : J ≤ vxConj x V) (hJL : L ≤ Subgroup.normalizer (J : Set G)) :
    J = ⊥ ∨ J = vxConj x V :=
  irr_vxConj (fun J hJV hJL' => S.vx_irr_eq_bot_or_eq J hJV hJL') hx J hJ hJL

theorem vx_L_le_normalizer (S : Setting G T L V) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    L ≤ Subgroup.normalizer ((vxConj x V : Subgroup G) : Set G) := by
  apply le_normalizer_of_forall
  intro l hl z hz
  rw [mem_vxConj] at hz ⊢
  have hl' : x⁻¹ * l * x ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) l).mp hl
    rwa [inv_inv] at h
  have key := Subgroup.mem_normalizer_iff.mp (S.frame.L_le hl') (x⁻¹ * z * x)
  have e : x⁻¹ * (l * z * l⁻¹) * x = (x⁻¹ * l * x) * (x⁻¹ * z * x) * (x⁻¹ * l * x)⁻¹ := by
    group
  rw [e]
  exact key.mp hz

theorem vx_le_pCoreOf (S : Setting G T L V) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) : vxConj x V ≤ pCoreOf 2 L :=
  vxConj_le (normalizer_le_normalizer_pCoreOf 2 L hx) S.V_le_pCoreOf_L

theorem vx_card (S : Setting G T L V) (x : G) : Nat.card ↥(vxConj x V) = 16 := by
  rw [card_vxConj, S.card_V]

theorem vx_comm (S : Setting G T L V) (x : G) {a b : G} (ha : a ∈ vxConj x V)
    (hb : b ∈ vxConj x V) : a * b = b * a := by
  rw [mem_vxConj] at ha hb
  have hc' := S.elemAbelian_V.1.is_comm.comm (⟨x⁻¹ * a * x, ha⟩ : ↥V) ⟨x⁻¹ * b * x, hb⟩
  have hc2 : x⁻¹ * a * x * (x⁻¹ * b * x) = x⁻¹ * b * x * (x⁻¹ * a * x) :=
    congrArg Subtype.val hc'
  calc a * b = x * (x⁻¹ * a * x * (x⁻¹ * b * x)) * x⁻¹ := by group
    _ = x * (x⁻¹ * b * x * (x⁻¹ * a * x)) * x⁻¹ := by rw [hc2]
    _ = b * a := by group

theorem vertex_excl (S : Setting G T L V) {B : Subgroup G}
    (hTB : T ≤ Subgroup.normalizer (B : Set G))
    (hBL : borelOf B T ≤ Subgroup.normalizer (L : Set G)) (h : Hyp111R L B T) :
    ¬ IsSpecialPow 2 4 2 ↥(pCoreOf 2 (L ⊔ bigB L B (Sp L B T))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hsp
  have hYT : Sp L B T ≤ T := S.Sp_le_T B
  have hBY : borelOf B (Sp L B T) = borelOf B T := S.borelOf_Sp_right h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := S.T_le_NL
  have hB2L : borelOf B (Sp L B T) ≤ Subgroup.normalizer (L : Set G) := by
    rw [hBY]
    exact hBL
  have hbigN : bigB L B (Sp L B T) ≤ Subgroup.normalizer (L : Set G) := by
    unfold bigB
    exact sup_le (sup_le ((F1.borelOf_le L _).trans Subgroup.le_normalizer) hB2L)
      (hYT.trans hTL)
  have hP1N : L ⊔ bigB L B (Sp L B T) ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hbigN
  set Y := Sp L B T with hYdef
  set B2 := borelOf B T with hB2def
  set P1 := L ⊔ bigB L B Y with hP1def
  set P := pCoreOf 2 P1 with hPdef
  have hP_le_P1 : P ≤ P1 := pCoreOf_le 2 P1
  have hPN : P1 ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 P1
  have hO2L : pCoreOf 2 L ≤ P :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (hP1N.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hVP : V ≤ P := S.V_le_pCoreOf_L.trans hO2L
  have hcardP : Nat.card ↥P = 1024 := by
    have h1 := hsp.2.1
    norm_num at h1
    exact h1
  have hZcard : Nat.card ↥(Subgroup.center ↥P) = 4 := hsp.2.2
  have hcomm_center : commutator ↥P = Subgroup.center ↥P := by
    rcases hsp.1.2 with ⟨hMC, -⟩ | ⟨hc, -, -⟩
    · exfalso
      have htop : Subgroup.center ↥P = ⊤ := by
        rw [eq_top_iff]
        intro z _
        exact Subgroup.mem_center_iff.mpr fun g => hMC.is_comm.comm g z
      rw [htop, Subgroup.card_top] at hZcard
      rw [hZcard] at hcardP
      norm_num at hcardP
    · exact hc
  obtain ⟨ZP, hZPdef⟩ : ∃ ZP : Subgroup G, ZP = (Subgroup.center ↥P).map P.subtype :=
    ⟨_, rfl⟩
  have mem_ZP : ∀ {z : G}, z ∈ ZP ↔ z ∈ P ∧ ∀ p ∈ P, z * p = p * z := by
    intro z
    rw [hZPdef]
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      refine ⟨w.2, fun p hp => ?_⟩
      have := Subgroup.mem_center_iff.mp hw ⟨p, hp⟩
      exact (congrArg Subtype.val this).symm
    · rintro ⟨hz, hc⟩
      refine Subgroup.mem_map.mpr ⟨⟨z, hz⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hc g.1 g.2).symm
  have hZPcard : Nat.card ↥ZP = 4 := by
    rw [hZPdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective P)]
    exact hZcard
  have hZP_le : ZP ≤ P := fun z hz => (mem_ZP.mp hz).1
  have hcomm_ZP : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ ZP := by
    intro a ha b hb
    have h1 : (⁅(⟨a, ha⟩ : ↥P), (⟨b, hb⟩ : ↥P)⁆ : ↥P) ∈ Subgroup.center ↥P := by
      rw [← hcomm_center]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hZPdef]
    refine Subgroup.mem_map.mpr ⟨_, h1, ?_⟩
    simp [commutatorElement_def]
  have hL_ZP : L ≤ Subgroup.normalizer (ZP : Set G) := by
    apply le_normalizer_of_forall
    intro l hl z hz
    obtain ⟨hzP, hzc⟩ := mem_ZP.mp hz
    have hlN : l ∈ Subgroup.normalizer (P : Set G) := hPN (Subgroup.mem_sup_left hl)
    rw [mem_ZP]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hlN z).mp hzP, fun p hp => ?_⟩
    have hq : l⁻¹ * p * l ∈ P := by
      refine (Subgroup.mem_normalizer_iff.mp hlN (l⁻¹ * p * l)).mpr ?_
      have e : l * (l⁻¹ * p * l) * l⁻¹ = p := by group
      rw [e]
      exact hp
    have hc := hzc (l⁻¹ * p * l) hq
    calc l * z * l⁻¹ * p = l * (z * (l⁻¹ * p * l)) * l⁻¹ := by group
      _ = l * ((l⁻¹ * p * l) * z) * l⁻¹ := by rw [hc]
      _ = p * (l * z * l⁻¹) := by group
  by_cases hA : B2 ≤ Subgroup.normalizer (V : Set G)
  ·
    have hbigV : bigB L B Y ≤ Subgroup.normalizer (V : Set G) := by
      unfold bigB
      exact sup_le (sup_le ((F1.borelOf_le L Y).trans S.frame.L_le) (by rw [hBY]; exact hA))
        (hYT.trans S.frame.T_le)
    have hP1V : P1 ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le hbigV
    have hPV : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ * v⁻¹ ∈ V := by
      intro p hp v hv
      have h1 : p * v * p⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hP1V (hP_le_P1 hp)) v).mp hv
      exact V.mul_mem h1 (V.inv_mem hv)
    have hU : V ⊓ ZP = ⊥ := by
      rcases S.vx_irr_eq_bot_or_eq (V ⊓ ZP) inf_le_left
          (le_normalizer_inf S.frame.L_le hL_ZP) with h3 | h3
      · exact h3
      · exfalso
        have hVZ : V ≤ ZP := inf_eq_left.mp h3
        have h4 := Subgroup.card_le_of_le hVZ
        rw [S.card_V, hZPcard] at h4
        norm_num at h4
    have hVbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have hvZ : v ∈ ZP := by
        rw [mem_ZP]
        refine ⟨hVP hv, fun p hp => ?_⟩
        have hc : p * v * p⁻¹ * v⁻¹ ∈ V ⊓ ZP := ⟨hPV p hp v hv, hcomm_ZP p hp v (hVP hv)⟩
        rw [hU, Subgroup.mem_bot] at hc
        have h2 : p * v * p⁻¹ = v := mul_inv_eq_one.mp hc
        calc v * p = (p * v * p⁻¹) * p := by rw [h2]
          _ = p * v := by group
      have hvU : v ∈ V ⊓ ZP := ⟨hv, hvZ⟩
      rw [hU, Subgroup.mem_bot] at hvU
      exact Subgroup.mem_bot.mpr hvU
    have h5 := S.card_V
    rw [hVbot, Subgroup.card_bot] at h5
    norm_num at h5
  ·
    obtain ⟨x, hxB2, hxV⟩ : ∃ x ∈ B2, x ∉ Subgroup.normalizer (V : Set G) := by
      by_contra hcon
      apply hA
      intro x hx
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := hBL hxB2
    obtain ⟨V', hV'def⟩ : ∃ V' : Subgroup G, V' = vxConj x V := ⟨_, rfl⟩
    have hV'L : L ≤ Subgroup.normalizer (V' : Set G) := by
      rw [hV'def]
      exact S.vx_L_le_normalizer hxL
    have hV'pC : V' ≤ pCoreOf 2 L := by
      rw [hV'def]
      exact S.vx_le_pCoreOf hxL
    have hV'P : V' ≤ P := hV'pC.trans hO2L
    have hV'L_le : V' ≤ L := hV'pC.trans (pCoreOf_le 2 L)
    have hV'irr : ∀ J : Subgroup G, J ≤ V' → L ≤ Subgroup.normalizer (J : Set G) →
        J = ⊥ ∨ J = V' := by
      intro J hJ hJL
      rw [hV'def] at hJ ⊢
      exact S.vx_irr_conj hxL J hJ hJL
    have hV'card : Nat.card ↥V' = 16 := by
      rw [hV'def]
      exact S.vx_card x
    have hV'comm : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := by
      intro a ha b hb
      rw [hV'def] at ha hb
      exact S.vx_comm x ha hb
    have hV'ne : V' ≠ V := by
      intro heq
      apply hxV
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hmem : x * h * x⁻¹ ∈ V' := by
          rw [hV'def, mem_vxConj]
          have e : x⁻¹ * (x * h * x⁻¹) * x = h := by group
          rw [e]
          exact hh
        rw [heq] at hmem
        exact hmem
      · intro hh
        have hmem : x * h * x⁻¹ ∈ V' := by
          rw [heq]
          exact hh
        rw [hV'def, mem_vxConj] at hmem
        have e : x⁻¹ * (x * h * x⁻¹) * x = h := by group
        rw [e] at hmem
        exact hmem
    have hVV' : V ⊓ V' = ⊥ := by
      rcases S.vx_irr_eq_bot_or_eq (V ⊓ V') inf_le_left
          (le_normalizer_inf S.frame.L_le hV'L) with h3 | h3
      · exact h3
      · exfalso
        have hle : V ≤ V' := inf_eq_left.mp h3
        apply hV'ne
        exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hV'card, S.card_V]))).symm
    have hcomm_VV' : ∀ a ∈ V, ∀ b ∈ V', a * b = b * a := fun a ha b hb =>
      commute_of_inf_eq_bot S.V_le_L hV'L_le S.frame.L_le hV'L hVV' ha hb
    have hcardW : Nat.card ↥(V ⊔ V') = 256 := by
      have h3 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V V' hcomm_VV').1
      rw [hVV', Subgroup.card_bot, S.card_V, hV'card] at h3
      omega
    have hWP : V ⊔ V' ≤ P := sup_le hVP hV'P
    have hWN_L : L ≤ Subgroup.normalizer ((V ⊔ V' : Subgroup G) : Set G) :=
      F1.le_normalizer_sup S.frame.L_le hV'L
    have hB4 : ∀ y ∈ B2, vxConj y V ≤ V ⊔ V' := by
      intro y hy
      by_contra hyW
      have hyL : y ∈ Subgroup.normalizer (L : Set G) := hBL hy
      have hUL : L ≤ Subgroup.normalizer ((vxConj y V : Subgroup G) : Set G) :=
        S.vx_L_le_normalizer hyL
      have hUpC : vxConj y V ≤ pCoreOf 2 L := S.vx_le_pCoreOf hyL
      have hUP : vxConj y V ≤ P := hUpC.trans hO2L
      have hUL_le : vxConj y V ≤ L := hUpC.trans (pCoreOf_le 2 L)
      have hUcard : Nat.card ↥(vxConj y V) = 16 := S.vx_card y
      have hVU : V ⊓ vxConj y V = ⊥ := by
        rcases S.vx_irr_eq_bot_or_eq (V ⊓ vxConj y V) inf_le_left
            (le_normalizer_inf S.frame.L_le hUL) with h3 | h3
        · exact h3
        · exfalso
          have hle : V ≤ vxConj y V := inf_eq_left.mp h3
          have hUV : vxConj y V = V :=
            (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hUcard, S.card_V]))).symm
          exact hyW (by rw [hUV]; exact le_sup_left)
      have hV'U : V' ⊓ vxConj y V = ⊥ := by
        rcases hV'irr (V' ⊓ vxConj y V) inf_le_left (le_normalizer_inf hV'L hUL) with h3 | h3
        · exact h3
        · exfalso
          have hle : V' ≤ vxConj y V := inf_eq_left.mp h3
          have hUV' : vxConj y V = V' :=
            (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hUcard, hV'card]))).symm
          exact hyW (by rw [hUV']; exact le_sup_right)
      have hirrU : ∀ J : Subgroup G, J ≤ vxConj y V → L ≤ Subgroup.normalizer (J : Set G) →
          J = ⊥ ∨ J = vxConj y V := fun J hJ hJL => S.vx_irr_conj hyL J hJ hJL
      have hcVU : ∀ a ∈ V, ∀ b ∈ vxConj y V, a * b = b * a := fun a ha b hb =>
        commute_of_inf_eq_bot S.V_le_L hUL_le S.frame.L_le hUL hVU ha hb
      have hcV'U : ∀ a ∈ V', ∀ b ∈ vxConj y V, a * b = b * a := fun a ha b hb =>
        commute_of_inf_eq_bot hV'L_le hUL_le hV'L hUL hV'U ha hb
      have hWU : V ⊔ V' ≤ Subgroup.centralizer ((vxConj y V : Subgroup G) : Set G) := by
        apply sup_le
        · intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          exact (hcVU a ha b hb).symm
        · intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          exact (hcV'U a ha b hb).symm
      have hWUinf : (V ⊔ V') ⊓ vxConj y V = ⊥ := by
        rcases hirrU ((V ⊔ V') ⊓ vxConj y V) inf_le_right
            (le_normalizer_inf hWN_L hUL) with h3 | h3
        · exact h3
        · exfalso
          exact hyW (inf_eq_right.mp h3)
      have hcard_WU := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (V ⊔ V')
        (vxConj y V) (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hWU ha) b hb).symm)).1
      rw [hWUinf, Subgroup.card_bot, hcardW, hUcard] at hcard_WU
      have hle : (V ⊔ V') ⊔ vxConj y V ≤ P := sup_le hWP hUP
      have h5 := Subgroup.card_le_of_le hle
      rw [hcardP] at h5
      omega
    have hB2N : B2 ≤ Subgroup.normalizer ((V ⊔ V' : Subgroup G) : Set G) := by
      intro y hy
      apply mem_normalizer_of_vxConj_le
      · rw [vxConj_sup, show vxConj y V' = vxConj (y * x) V by rw [hV'def, vxConj_vxConj]]
        exact sup_le (hB4 y hy) (hB4 (y * x) (B2.mul_mem hy hxB2))
      · rw [vxConj_sup, show vxConj y⁻¹ V' = vxConj (y⁻¹ * x) V by
          rw [hV'def, vxConj_vxConj]]
        exact sup_le (hB4 y⁻¹ (B2.inv_mem hy))
          (hB4 (y⁻¹ * x) (B2.mul_mem (B2.inv_mem hy) hxB2))
    have hTB2 : T ≤ Subgroup.normalizer (B2 : Set G) := T_le_normalizer_borelOf_gen hTB
    have hT_conj : ∀ t ∈ T, vxConj t (V ⊔ V') ≤ V ⊔ V' := by
      intro t ht
      rw [vxConj_sup]
      apply sup_le
      · exact (vxConj_le (S.frame.T_le ht) le_rfl).trans le_sup_left
      · have hxt : t * x * t⁻¹ ∈ B2 := (Subgroup.mem_normalizer_iff.mp (hTB2 ht) x).mp hxB2
        have e : vxConj t V' = vxConj (t * x * t⁻¹) (vxConj t V) := by
          rw [hV'def, vxConj_vxConj, vxConj_vxConj]
          congr 1
          group
        rw [e]
        exact (vxConj_mono (vxConj_le (S.frame.T_le ht) le_rfl)).trans (hB4 _ hxt)
    have hWT : T ≤ Subgroup.normalizer ((V ⊔ V' : Subgroup G) : Set G) := by
      intro t ht
      apply mem_normalizer_of_vxConj_le
      · exact hT_conj t ht
      · exact hT_conj t⁻¹ (T.inv_mem ht)
    have hWP1 : P1 ≤ Subgroup.normalizer ((V ⊔ V' : Subgroup G) : Set G) := by
      rw [hP1def]
      apply sup_le hWN_L
      unfold bigB
      exact sup_le (sup_le ((F1.borelOf_le L Y).trans hWN_L) (by rw [hBY]; exact hB2N))
        (hYT.trans hWT)
    have hWnormal : ((V ⊔ V' : Subgroup G).subgroupOf P).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hWP]
      intro h k hh hk
      exact (Subgroup.mem_normalizer_iff.mp (hWP1 (hP_le_P1 hk)) h).mp hh
    haveI := hWnormal
    have hquot : Nat.card (↥P ⧸ (V ⊔ V' : Subgroup G).subgroupOf P) = 4 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((V ⊔ V' : Subgroup G).subgroupOf P)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv, hcardW, hcardP] at h1
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hMC : IsMulCommutative (↥P ⧸ (V ⊔ V' : Subgroup G).subgroupOf P) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hquot]; norm_num)
    have hcommW : ∀ u ∈ P, ∀ v ∈ P, u * v * u⁻¹ * v⁻¹ ∈ V ⊔ V' := by
      intro u hu v hv
      have hcomm : (QuotientGroup.mk (⟨v⁻¹, P.inv_mem hv⟩ : ↥P) :
            ↥P ⧸ (V ⊔ V' : Subgroup G).subgroupOf P) *
          QuotientGroup.mk (⟨u⁻¹, P.inv_mem hu⟩ : ↥P) =
          QuotientGroup.mk (⟨u⁻¹, P.inv_mem hu⟩ : ↥P) *
          QuotientGroup.mk (⟨v⁻¹, P.inv_mem hv⟩ : ↥P) :=
        hMC.is_comm.comm _ _
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hcomm
      have h3 := QuotientGroup.eq.mp hcomm
      rw [Subgroup.mem_subgroupOf] at h3
      simpa [mul_assoc] using h3
    have hZW : ZP ≤ V ⊔ V' := by
      intro z hz
      obtain ⟨hzP, hzc⟩ := mem_ZP.mp hz
      have hzc' : (⟨z, hzP⟩ : ↥P) ∈ Subgroup.center ↥P := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact (hzc g.1 g.2).symm
      rw [← hcomm_center] at hzc'
      have hC : commutator ↥P ≤ (V ⊔ V' : Subgroup G).subgroupOf P := by
        apply Subgroup.commutator_le.mpr
        intro a _ b _
        rw [Subgroup.mem_subgroupOf]
        have h3 := hcommW a.1 a.2 b.1 b.2
        simpa [commutatorElement_def] using h3
      exact Subgroup.mem_subgroupOf.mp (hC hzc')
    have hZV : ZP ⊓ V = ⊥ := by
      rcases S.vx_irr_eq_bot_or_eq (ZP ⊓ V) inf_le_right
          (le_normalizer_inf hL_ZP S.frame.L_le) with h3 | h3
      · exact h3
      · exfalso
        have hle : V ≤ ZP := inf_eq_right.mp h3
        have h4 := Subgroup.card_le_of_le hle
        rw [S.card_V, hZPcard] at h4
        norm_num at h4
    have hcard_M : Nat.card ↥(ZP ⊔ V) = 64 := by
      have h3 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute ZP V
        (fun a ha b hb => (mem_ZP.mp ha).2 b (hVP hb))).1
      rw [hZV, Subgroup.card_bot, hZPcard, S.card_V] at h3
      omega
    have hMW : ZP ⊔ V ≤ V ⊔ V' := sup_le hZW le_sup_left
    have hVV'C : V ⊔ V' ≤ Subgroup.centralizer ((V' : Subgroup G) : Set G) := by
      apply sup_le
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hcomm_VV' a ha b hb).symm
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact hV'comm b hb a ha
    have hMM' : (ZP ⊔ V) ⊓ V' = ⊥ ∨ (ZP ⊔ V) ⊓ V' = V' :=
      hV'irr ((ZP ⊔ V) ⊓ V') inf_le_right
        (le_normalizer_inf (F1.le_normalizer_sup hL_ZP S.frame.L_le) hV'L)
    rcases hMM' with h3 | h3
    · have hcomm' := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (ZP ⊔ V) V'
        (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hVV'C (hMW ha)) b hb).symm)).1
      rw [h3, Subgroup.card_bot, hcard_M, hV'card] at hcomm'
      have h5 := Subgroup.card_le_of_le
        (sup_le hMW le_sup_right : (ZP ⊔ V) ⊔ V' ≤ V ⊔ V')
      rw [hcardW] at h5
      omega
    · have hle : V' ≤ ZP ⊔ V := inf_eq_right.mp h3
      have h5 := Subgroup.card_le_of_le (sup_le le_sup_right hle : V ⊔ V' ≤ ZP ⊔ V)
      rw [hcardW, hcard_M] at h5
      omega

end Setting

end CFSG.Quasithin.H13.A5
