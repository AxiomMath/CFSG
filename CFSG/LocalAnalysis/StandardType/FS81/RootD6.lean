module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogDefs
public import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs
public import CFSG.LocalAnalysis.StandardType.FS81.RootE8
public import CFSG.LocalAnalysis.StandardType.FS81.S7Fusion
public import CFSG.LocalAnalysis.StandardType.FS81.RootFusionGen
public import CFSG.Blueprint.ChevalleyRootGroups

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.QuasithinUnique

private theorem orderOf_psi_eq {G A : Type} [Group G] [Group A] {Y : Subgroup G}
    (ψ : A ≃* ↥Y) (a : A) : orderOf (((ψ a : ↥Y) : G)) = orderOf a :=
  (Subgroup.orderOf_coe (ψ a)).trans (MulEquiv.orderOf_eq ψ a)

private theorem orderOf_root_of_conj {G A : Type} [Group G] [Group A] {Y : Subgroup G}
    (ψ : A ≃* ↥Y) {r : A} {b y : G} (hb : orderOf b = 3)
    (h : ((ψ r : ↥Y) : G) = y * b * y⁻¹) : orderOf r = 3 := by
  have himg : orderOf (((ψ r : ↥Y) : G)) = 3 := by
    rw [h, show orderOf (y * b * y⁻¹) = orderOf b from by
      simpa using (MulAut.conj y).orderOf_eq b, hb]
  exact (orderOf_psi_eq ψ r).symm.trans himg

private theorem charTwo_centralizer_image {G A : Type} [Group G] [Group A] {Y : Subgroup G}
    (hchar : IsCharTwoType G) (ψ : A ≃* ↥Y) {s : A} (hs : orderOf s = 2) :
    CharTwo (Subgroup.centralizer ({((ψ s : ↥Y) : G)} : Set G)) :=
  centralizer_inf_le_pCoreOf_of_isCharTwoType hchar ((orderOf_psi_eq ψ s).trans hs)

private theorem two_dvd_card_adjoint_E7 :
    2 ∣ Nat.card (adjointGroup .E7 (ZMod 2)) := by
  let x : adjointGroup .E7 (ZMod 2) :=
    ⟨pinnedX .E7 (ZMod 2) (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1) 1,
      pinnedX_mem_adjointGroup _ _⟩
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : pinnedX .E7 (ZMod 2) (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1) 1 =
        pinnedX .E7 (ZMod 2) (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1) 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (pinnedX_injective .E7 (ZMod 2) _ h1)
  have hx2 : x ^ 2 = 1 := by
    refine Subtype.ext ?_
    change pinnedX .E7 (ZMod 2) (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1) 1 *
      pinnedX .E7 (ZMod 2) (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1) 1 = 1
    rw [← pinnedX_add, show (1 : ZMod 2) + 1 = 0 by decide, pinnedX_zero]
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  simpa [hxo] using orderOf_dvd_natCard x

private theorem exists_sylow_center_involution (X : Type) [Group X] [Finite X]
    (h2 : 2 ∣ Nat.card X) :
    ∃ (P : Sylow 2 X) (t : X), t ∈ (P : Subgroup X) ∧
      (∀ s ∈ (P : Subgroup X), s * t = t * s) ∧ orderOf t = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hfac : 0 < (Nat.card X).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
  haveI hnt : Nontrivial (P : Subgroup X) := by
    rw [← Finite.one_lt_card_iff_nontrivial, Sylow.card_eq_multiplicity P]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Nat.card X).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
  obtain ⟨c, hcZ, hc1⟩ : ∃ c ∈ Subgroup.center (P : Subgroup X), c ≠ 1 := by
    obtain ⟨c, hc, hcn⟩ := SetLike.exists_of_lt (IsPGroup.bot_lt_center (P.isPGroup'))
    exact ⟨c, hc, fun h => hcn (by rw [Subgroup.mem_bot]; exact h)⟩
  have hdvd : 2 ∣ orderOf c := IsPGroup.dvd_orderOf (P.isPGroup') hc1
  have hZdvd : 2 ∣ Nat.card (Subgroup.center (P : Subgroup X)) := by
    have h1 : orderOf (⟨c, hcZ⟩ : Subgroup.center (P : Subgroup X)) = orderOf c :=
      (Subgroup.orderOf_coe ⟨c, hcZ⟩).symm
    exact dvd_trans hdvd (h1 ▸ orderOf_dvd_natCard _)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hZdvd
  refine ⟨P, (w : (P : Subgroup X)), w.1.2, ?_, ?_⟩
  · intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 w.2 ⟨x, hx⟩)
  · exact (Subgroup.orderOf_coe w.1).trans ((Subgroup.orderOf_coe w).trans hw)

private theorem exists_sylow_center_involution_top (G : Type) [Group G] [Finite G]
    (h2 : 2 ∣ Nat.card G) :
    ∃ (S : Subgroup G) (t : G), IsSylow2In S (⊤ : Subgroup G) ∧ t ∈ S ∧ orderOf t = 2 ∧
      (∀ s ∈ S, s * t = t * s) ∧
      ∀ g : G, g * t * g⁻¹ ∈ (⊤ : Subgroup G) → g ∈ (⊤ : Subgroup G) := by
  have h2' : 2 ∣ Nat.card ↥(⊤ : Subgroup G) := by
    rw [Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv]
    exact h2
  obtain ⟨P, t, htP, htcent, ht2⟩ :=
    exists_sylow_center_involution ↥(⊤ : Subgroup G) h2'
  refine ⟨(P : Subgroup ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype,
    ((t : ↥(⊤ : Subgroup G)) : G), isSylow2In_map_subtype P, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem (⊤ : Subgroup G).subtype htP
  · exact (Subgroup.orderOf_coe t).trans ht2
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hs
    simpa using congrArg Subtype.val (htcent u hu)
  · intro g _
    exact Subgroup.mem_top g

theorem l3RootFusionAt_D6_of_recog
    (hRec : E7RootRecog) (hM : IsEmSevenModel) (hEl : D6RootEltAt) (hC : RowCentAt Row.D6)
    (hT : E8TorusAt Row.D6) (hA : E8AutAt Row.D6) : L3RootFusionAt Row.D6 := by
  intro G _ _ b₀ K E hstd hchar B hB hrec hfus Y hY hcap hcore
  have h : RootSetting Row.D6 b₀ K E B Y := ⟨hstd, hchar, hB, hrec, hfus, hY, hcap, hcore⟩
  obtain ⟨ψ⟩ := hM G Y h.isEm
  obtain ⟨r, hr, y, hy, hψr⟩ := hEl G b₀ K E B Y h ψ
  have hr3 : orderOf r = 3 := orderOf_root_of_conj ψ h.std.2.1.1.1 hψr
  obtain ⟨R, hRC, hRn, hR3, hCR⟩ := hC G b₀ K E h.std B h.adapted h.recOut h.fus
  have hRY : R ≤ Subgroup.centralizer (Y : Set G) := h.core R hRC hRn hR3
  have hCeq : Subgroup.centralizer ({b₀} : Set G) =
      R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y) :=
    calc Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K) := hCR
      _ = R ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Y) := by rw [h.cap]
  have hfusY : ∀ g : G, g * b₀ * g⁻¹ ∈ Y →
      ∃ y' ∈ Y, g * b₀ * g⁻¹ = y' * b₀ * y'⁻¹ :=
    fun g hg => h.exists_conj_eq_of_conj_mem hA hT hg
  have hCharR : ∀ t ∈ R, orderOf t = 2 →
      CharTwo (Subgroup.centralizer ({t} : Set G)) :=
    fun t _ ht => centralizer_inf_le_pCoreOf_of_isCharTwoType h.charTwo ht
  have hCharS : ∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) →
      orderOf s = 2 →
      CharTwo (Subgroup.centralizer ({((ψ s : ↥Y) : G)} : Set G)) :=
    fun s _ hs2 => charTwo_centralizer_image h.charTwo ψ hs2
  have hYtop : Y = ⊤ :=
    hRec G Y R ψ r b₀ hr hr3 ⟨y, hy, hψr⟩ hRY hR3 hCeq hfusY hCharR hCharS
  rw [hYtop]
  have h2G : 2 ∣ Nat.card G := by
    rw [← Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv, ← hYtop,
      ← Nat.card_congr ψ.toEquiv]
    exact two_dvd_card_adjoint_E7
  exact exists_sylow_center_involution_top G h2G

end CFSG.StandardType.FrameRoute.FS81
