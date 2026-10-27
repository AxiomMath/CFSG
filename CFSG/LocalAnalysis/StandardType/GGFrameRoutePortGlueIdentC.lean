module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9SpAmbient
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9SignLin
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.BilinearForm.Prod
import CFSG.Quasithin.Vol2.Ch7Prop711Facts
public import CFSG.LocalAnalysis.StandardType.GGAutomizerEquiv
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9SpCover
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9LinearAmbient
import CFSG.GH74.E2.DirectProd
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCBShearAxis
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType.FrameRoute

open Multiplicative CFSG.StandardType.ChoiceTwo

variable {G : Type} [Group G] {Bs : Subgroup G} {z : G}

theorem signedB6At_of_split_torus
    (T : Multiplicative (Fin 6 → ZMod 3) →* G) (hT : Function.Injective T)
    (hsplit : Bs = Subgroup.zpowers z ⊔ T.range)
    (hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ T.range, a * b = b * a)
    (hdisj : Subgroup.zpowers z ⊓ T.range = ⊥)
    (hupper : ∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∃ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool), ∀ f,
        g * T (ofAdd f) * g⁻¹ = T (ofAdd (moveExp π η f)))
    (hlower : ∀ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool),
      ∃ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ f, g * T (ofAdd f) * g⁻¹ = T (ofAdd (moveExp π η f))) :
    GGSignedB6At Bs z := by
  classical
  let Z := Subgroup.zpowers z
  let τ : Multiplicative (Fin 6 → ZMod 3) ≃* T.range := MonoidHom.ofInjective hT
  let ξ : (Z × T.range) ≃* Bs :=
    (CFSG.GH74.E2.prodSupEquiv Z T.range hcomm hdisj).trans
      (MulEquiv.subgroupCongr hsplit.symm)
  have hξ : ∀ p : Z × T.range, (ξ p : G) = (p.1 : G) * (p.2 : G) := by
    intro p
    exact CFSG.GH74.E2.prodSupEquiv_apply Z T.range hcomm hdisj p
  let ν : Bs →* Multiplicative (Fin 6 → ZMod 3) :=
    τ.symm.toMonoidHom.comp ((MonoidHom.snd Z T.range).comp ξ.symm.toMonoidHom)
  let u : G → Fin 6 → ZMod 3 := fun b => if hb : b ∈ Bs then toAdd (ν ⟨b, hb⟩) else 0
  have hu : ∀ b : Bs, u b = toAdd (ν b) := fun b => by simp [u, b.property]
  have hνξ : ∀ p : Z × T.range, ν (ξ p) = τ.symm p.2 := by
    intro p
    simp [ν]
  have hτ : ∀ q : T.range, T (τ.symm q) = (q : G) := by
    intro q
    exact congrArg Subtype.val (τ.apply_symm_apply q)
  have hproj : ∀ (a : Z) (f : Fin 6 → ZMod 3), u ((a : G) * T (ofAdd f)) = f := by
    intro a f
    have hp : (ξ (a, τ (ofAdd f)) : G) = (a : G) * T (ofAdd f) := hξ _
    rw [← hp, hu, hνξ, MulEquiv.symm_apply_apply]
    rfl
  have hdec : ∀ b : Bs, ∃ a : Z, (b : G) = (a : G) * T (ofAdd (u b)) := by
    intro b
    have hp : ∀ p : Z × T.range,
        (ξ p : G) = (p.1 : G) * T (ofAdd (u (ξ p))) := by
      intro p
      rw [hu, hνξ]
      change (ξ p : G) = (p.1 : G) * T (τ.symm p.2)
      rw [hξ, hτ]
    exact ⟨(ξ.symm b).1, by simpa only [MulEquiv.apply_symm_apply] using hp (ξ.symm b)⟩
  have hzero : T (ofAdd (0 : Fin 6 → ZMod 3)) = 1 := T.map_one
  have hact : ∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∀ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool),
        (∀ f, g * T (ofAdd f) * g⁻¹ = T (ofAdd (moveExp π η f))) →
        ∀ b : Bs, u (g * b * g⁻¹) = moveExp π η (u b) := by
    intro g hg π η hπη b
    obtain ⟨a, ha⟩ := hdec b
    have hzg : z ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hg.2).symm
    have hga : g * (a : G) = (a : G) * g :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        ((Subgroup.zpowers_le.mpr hzg) a.property)).symm
    have hb : g * (b : G) * g⁻¹ = (a : G) * (g * T (ofAdd (u b)) * g⁻¹) := by
      conv_lhs => rw [ha]
      calc g * ((a : G) * T (ofAdd (u b))) * g⁻¹ =
          (g * (a : G)) * T (ofAdd (u b)) * g⁻¹ := by group
        _ = (a : G) * (g * T (ofAdd (u b)) * g⁻¹) := by rw [hga]; group
    rw [hb, hπη, hproj]
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb b' hb'
    change u (((⟨b, hb⟩ : Bs) * ⟨b', hb'⟩ : Bs) : G) =
      u ((⟨b, hb⟩ : Bs) : G) + u ((⟨b', hb'⟩ : Bs) : G)
    rw [hu, hu, hu, map_mul]
    rfl
  · intro b hb
    constructor
    · intro hb0
      obtain ⟨a, ha⟩ := hdec ⟨b, hb⟩
      rw [hb0, hzero, mul_one] at ha
      change b = (a : G) at ha
      rw [ha]
      exact a.property
    · intro hbZ
      simpa only [hzero, mul_one] using hproj ⟨b, hbZ⟩ 0
  · intro f
    have hTBs : T.range ≤ Bs := by rw [hsplit]; exact le_sup_right
    refine ⟨T (ofAdd f), hTBs ⟨ofAdd f, rfl⟩, ?_⟩
    simpa only [OneMemClass.coe_one, one_mul] using hproj (1 : Z) f
  · intro g hg
    obtain ⟨π, η, hπη⟩ := hupper g hg
    exact ⟨π, η, fun b hb => hact g hg π η hπη ⟨b, hb⟩⟩
  · intro π η
    obtain ⟨g, hg, hπη⟩ := hlower π η
    exact ⟨g, hg, fun b hb => hact g hg π η hπη ⟨b, hb⟩⟩

theorem signedB6At_of_native_sp_six [Finite G] {K : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (e : K ≃* CFSG.Open.StatedSp 6 F) (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G)) : GGSignedB6At Bs z := by
  obtain ⟨⟨L, hL, hFL, hfin, ζ, P, -, hζ, hPs⟩, -⟩ :=
    exists_spFrame_of_native_sp_bstar (by norm_num : 3 ≤ 6) hF e hBs hN hker hBstar
  letI : Field L := hL
  letI : Algebra F L := hFL
  letI : Module.Finite F L := hfin
  have hPsize : P.s = 6 := hPs
  have hdata := native_sp_torus_action_data (by norm_num : 3 ≤ 6)
    hF e hBs hN hker hBstar hNK P hζ
  have hdata6 : ∃ T : Multiplicative (Fin 6 → ZMod 3) →* G, Function.Injective T ∧
      T.range = Bs ⊓ K ∧
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∃ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool), ∀ f,
          g * T (ofAdd f) * g⁻¹ = T (ofAdd (moveExp π η f))) ∧
      ∀ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool),
        ∃ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
          ∀ f, g * T (ofAdd f) * g⁻¹ = T (ofAdd (moveExp π η f)) := by
    rw [← hPsize]
    exact hdata
  obtain ⟨T, hT, hrange, hupper, hlower⟩ := hdata6
  have hsplit : Bs = Subgroup.zpowers z ⊔ T.range := by
    rw [hrange]
    exact bstar_eq_zpowers_sup_inf_of_native_sp (by norm_num : 3 ≤ 6)
      hF e hBs hN hker hBstar
  have hZK : Subgroup.zpowers z ≤ Subgroup.centralizer (K : Set G) := by
    rw [← hker]
    exact inf_le_right
  have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ T.range, a * b = b * a := by
    intro a ha b hb
    rw [hrange] at hb
    exact ((Subgroup.mem_centralizer_iff.mp (hZK ha)) b hb.2).symm
  have hcenter : Subgroup.center K = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (by norm_num : 1 ≤ 6),
      Subgroup.card_bot]
  have hdisj : Subgroup.zpowers z ⊓ T.range = ⊥ := by
    refine le_antisymm (fun b hb => ?_) bot_le
    have hbK : b ∈ K := (hrange ▸ hb.2).2
    have hbZ : (⟨b, hbK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun k => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hZK hb.1)) k k.property)
    rw [hcenter, Subgroup.mem_bot] at hbZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hbZ)
  exact signedB6At_of_split_torus T hT hsplit hcomm hdisj hupper hlower

theorem false_of_native_sp_seven [Finite G] {K : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (e : K ≃* CFSG.Open.StatedSp 7 F) (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (W : Subgroup (MulAut (ggGamma K hN).range))
    (hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut K)) (ggGamma K hN).range)
    (hWord : Nat.card W = 2903040) : False := by
  obtain ⟨⟨L, hL, hFL, hfin, ζ, P, -, hζ, hPs⟩, -⟩ :=
    exists_spFrame_of_native_sp_bstar (by norm_num : 3 ≤ 7) hF e hBs hN hker hBstar
  letI : Field L := hL
  letI : Algebra F L := hFL
  letI : Module.Finite F L := hfin
  have hsize : P.s = 7 := hPs
  have hdvd := P.card_automizer_inner_torus_dvd (by norm_num : 3 ≤ 7) hF hζ
  rw [hsize] at hdvd
  have hsplit := bstar_eq_zpowers_sup_inf_of_native_sp (by norm_num : 3 ≤ 7)
    hF e hBs hN hker hBstar
  have himage := map_range_ggGamma_of_split_model e hN hker hsplit
  have hcard := card_ggAutomizer_top_map_equiv (MulAut.congr e) (ggGamma K hN).range
  rw [himage] at hcard
  have hdvd' : Nat.card (ggAutomizer (⊤ : Subgroup (MulAut K)) (ggGamma K hN).range) ∣
      2 ^ 7 * Nat.factorial 7 := by
    rw [← hcard]
    exact hdvd
  exact P9_Wa_nonunitary_n8_false hW hWord hdvd'

theorem n_eq_seven_signedB6At_of_native_sp [Finite G] {K : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {a n : ℕ}
    (ha : 3 ≤ a) (hF : Nat.card F = 2) (e : K ≃* CFSG.Open.StatedSp a F)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n)
    (hn : n = 7 ∨ n = 8) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (W : Subgroup (MulAut (ggGamma K hN).range))
    (hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut K)) (ggGamma K hN).range)
    (hWord : Nat.card W = if n = 7 then 23040 else 2903040) :
    n = 7 ∧ GGSignedB6At Bs z := by
  have harank := native_sp_rank_eq_of_card_bstar ha hF e hBs hcard hz hz1 hN hker hBstar
  rcases hn with rfl | rfl
  · have ha6 : a = 6 := by omega
    subst a
    exact ⟨rfl, signedB6At_of_native_sp_six hF e hBs hN hker hBstar hNK⟩
  · have ha7 : a = 7 := by omega
    subst a
    exact (false_of_native_sp_seven hF e hBs hN hker hBstar W hW
      (by simpa using hWord)).elim

theorem n_eq_seven_signedB6At_of_sp_label
    [Finite G] {K : Subgroup G} {S : ℕ → CFSG.Assembly.LargeEvenLabel → Prop} {n : ℕ}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n)
    (hn : n = 7 ∨ n = 8) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hS : ∀ lab, S 3 lab → (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K)
    (W : Subgroup (MulAut (ggGamma K hN).range))
    (hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut K)) (ggGamma K hN).range)
    (hWord : Nat.card W = if n = 7 then 23040 else 2903040) :
    n = 7 ∧ GGSignedB6At Bs z := by
  obtain ⟨a, F, hfield, hfin, hchar, e, ha, hF, hRank⟩ :=
    native_sp_equiv_of_innerDiagOnLabel hBs hcard hn hz hz1 hN hker hBstar hS hK
  letI : Field F := hfield
  letI : Finite F := hfin
  letI : CharP F 2 := hchar
  exact n_eq_seven_signedB6At_of_native_sp (by omega) hF e hBs hcard hn hz hz1
    hN hNK hker hBstar W hW hWord

theorem signedB6At_of_actor_torus_weight [Finite G] {K : Subgroup G}
    (D : LinTwoTB.TorusData K 6)
    (hZ : ∀ g h : K, MulAut.conj g = MulAut.conj h → g = h)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hA : D.IsTorusAut (ggGamma K hN).range)
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (wt : K → ℕ) {c : ℕ} (hc : 0 < c)
    (hw : ∀ v, wt (D.el v) = c * LinTwoTv.hamWt v)
    (hwt : ∀ (α : MulAut K) k, wt (α k) = wt k) : GGSignedB6At Bs z := by
  classical
  let T : Multiplicative (Fin 6 → ZMod 3) →* G := K.subtype.comp D.ι
  have hT : Function.Injective T := fun v w h => D.inj (Subtype.ext h)
  let U : Subgroup K := D.ι.range
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    rintro u ⟨v, rfl⟩
    exact D.el_cube (toAdd v)
  have hUA : U.map (MulAut.conj : K →* MulAut K) = (ggGamma K hN).range := by
    ext α
    rw [hA]
    constructor
    · rintro ⟨u, ⟨v, rfl⟩, h⟩
      exact ⟨toAdd v, h.symm⟩
    · rintro ⟨v, rfl⟩
      exact Subgroup.mem_map.mpr ⟨D.el v, D.mem_tor.mpr ⟨v, rfl⟩, rfl⟩
  have hTmap : T.range = U.map K.subtype := by
    change (K.subtype.comp D.ι).range = U.map K.subtype
    rw [MonoidHom.range_comp]
  have hdata := bstar_split_of_inner_subgroup U hZ hBs hN hUA hU3 hBstar hker
  rw [← hTmap] at hdata
  have hrange : T.range = Bs ⊓ K := hdata.1
  have hsplit : Bs = Subgroup.zpowers z ⊔ T.range := hdata.2.1
  have hdisj : Subgroup.zpowers z ⊓ T.range = ⊥ := hdata.2.2
  have hDmem : ∀ v, (D.el v : G) ∈ Bs := by
    intro v
    have hv : T (ofAdd v) ∈ T.range := ⟨ofAdd v, rfl⟩
    rw [hrange] at hv
    exact hv.1
  have hZK : Subgroup.zpowers z ≤ Subgroup.centralizer (K : Set G) := by
    rw [← hker]
    exact inf_le_right
  have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ T.range, a * b = b * a := by
    intro a ha b hb
    rw [hrange] at hb
    exact ((Subgroup.mem_centralizer_iff.mp (hZK ha)) b hb.2).symm
  have hupper : ∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∃ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool), ∀ v,
        g * T (ofAdd v) * g⁻¹ = T (ofAdd (moveExp π η v)) := by
    intro g hg
    let α : MulAut K := K.normalizerMonoidHom ⟨g, hNK hg⟩
    have hconj : ∀ k : K, (α k : G) = g * (k : G) * g⁻¹ := fun k =>
      Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨g, hNK hg⟩ k
    have hαv : ∀ v, α (D.el v) ∈ D.ι.range := by
      intro v
      have hb : (α (D.el v) : G) ∈ Bs := by
        rw [hconj]
        exact (Subgroup.mem_normalizer_iff.mp hg.1 _).mp (hDmem v)
      have hTmem : (α (D.el v) : G) ∈ T.range := by
        rw [hrange]
        exact ⟨hb, (α (D.el v)).property⟩
      obtain ⟨f, hf⟩ := hTmem
      exact ⟨f, Subtype.ext hf⟩
    have hα : α ∈ Subgroup.normalizer ((ggGamma K hN).range : Set (MulAut K)) := by
      apply CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_forall_conj_mem
      intro a ha
      obtain ⟨v, rfl⟩ := (hA a).mp ha
      rw [CFSG.mulAut_conj_mul_inv]
      obtain ⟨f, hf⟩ := hαv v
      exact (hA _).mpr ⟨toAdd f, by rw [← hf]; rfl⟩
    obtain ⟨Θ, hΘ⟩ := exists_actor_equiv_of_torusData D hZ hA
    obtain ⟨π, η, hmove⟩ := exists_moveExp_of_torus_weight_action D wt hc hw hwt α _
      (torus_action_of_normalizer_actor D hZ Θ hΘ α hα)
    refine ⟨π, η, fun v => ?_⟩
    change g * (D.el v : G) * g⁻¹ = (D.el (moveExp π η v) : G)
    rw [← hconj]
    exact congrArg Subtype.val (hmove v)
  have hlower : ∀ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool),
      ∃ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ v, g * T (ofAdd v) * g⁻¹ = T (ofAdd (moveExp π η v)) := by
    intro π η
    obtain ⟨k, hk⟩ := exists_conj_moveExp_of_torusData D π η
    let g : G := k
    have hgT : ∀ v, g * T (ofAdd v) * g⁻¹ = T (ofAdd (moveExp π η v)) := by
      intro v
      exact congrArg Subtype.val (hk v)
    have hzK : z ∈ Subgroup.centralizer (K : Set G) :=
      hZK (Subgroup.mem_zpowers z)
    have hgc : g ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hzK) g k.property)
    have hzg : z ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm
    have hgZ : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
      apply CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_forall_conj_mem
      intro t ht
      have hgt : g * t = t * g :=
        (Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hzg) ht)).symm
      rw [hgt, mul_assoc, mul_inv_cancel, mul_one]
      exact ht
    have hgE : g ∈ Subgroup.normalizer (T.range : Set G) := by
      apply CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_forall_conj_mem
      rintro t ⟨v, rfl⟩
      exact ⟨ofAdd (moveExp π η (toAdd v)), (hgT (toAdd v)).symm⟩
    have hgBs : g ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [hsplit]
      exact (Subgroup.normalizer_inf_normalizer_le_normalizer_sup
        (Subgroup.zpowers z) T.range) ⟨hgZ, hgE⟩
    exact ⟨g, ⟨hgBs, hgc⟩, hgT⟩
  exact signedB6At_of_split_torus T hT hsplit hcomm hdisj hupper hlower

theorem n_eq_seven_signedB6At_of_linear_label [Finite G] {K : Subgroup G} {n : ℕ}
    {S : ℕ → CFSG.Assembly.LargeEvenLabel → Prop}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : n = 7 ∨ n = 8)
    (hz : z ∈ Bs) (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hS : ∀ lab, S 3 lab → lab.tag = .A ∧ lab.n = 1)
    (hK : GGInnerDiagOnLabel S 3 Bs K)
    (W : Subgroup (MulAut (ggGamma K hN).range))
    (hW : W ≤ ggAutomizer (⊤ : Subgroup (MulAut K)) (ggGamma K hN).range)
    (hWord : Nat.card W = if n = 7 then 23040 else 2903040) :
    n = 7 ∧ GGSignedB6At Bs z := by
  obtain ⟨s, c, D, wt, hZ, hA, hc, hw, hwt, hs⟩ :=
    exists_linear_torusData_of_innerDiagOnLabel hBs hcard hn hz hz1 hN hker hBstar hS hK
  rcases hn with hn | hn
  · have hs6 : s = 6 := by omega
    subst s
    exact ⟨hn, signedB6At_of_actor_torus_weight D hZ hBs hN hA hker hBstar hNK wt hc hw hwt⟩
  · have hs7 : s = 7 := by omega
    subst s
    have hb := card_automizer_actor_torus_dvd D hZ hA wt hc hw hwt
    have hb' : Nat.card (ggAutomizer (⊤ : Subgroup (MulAut K)) (ggGamma K hN).range) ∣
        645120 := by norm_num at hb; exact hb
    have hWord8 : Nat.card W = 2903040 := by rw [hWord, hn]; norm_num
    exact False.elim (P9_Wa_nonunitary_n8_false hW hWord8 hb')

end CFSG.StandardType.FrameRoute

end
