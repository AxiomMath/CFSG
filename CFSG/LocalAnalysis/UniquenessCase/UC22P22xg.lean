module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xf
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22x

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.Open.StatedAPI
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace P22x

section Group

theorem commutator_le_of_normalizer {U A B : Subgroup G} (hA : A ≤ U)
    (hB : B ≤ normalizer (U : Set G)) : ⁅A, B⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  have h1 : b * a⁻¹ * b⁻¹ ∈ U := (mem_normalizer_iff.1 (hB hb) a⁻¹).1 (U.inv_mem (hA ha))
  have := U.mul_mem (hA ha) h1
  simpa [mul_assoc] using this

theorem proofIi_le (D : Data G) {Ni : Subgroup G} (hNi : Ni ≤ D.M) : proofIi D Ni ≤ D.U := by
  have hV := uc22p22xf_hV D
  have hN : proofN D ≤ D.M := uc22p22e_jOf_le_self D.M
  exact commutator_le_of_normalizer (commutator_le_of_normalizer le_rfl (hN.trans hV)) (hNi.trans hV)

theorem proofEiHat_le (D : Data G) {Ni : Subgroup G} (hNi : Ni ≤ D.M) : proofEiHat D Ni ≤ D.U :=
  commutator_le_of_normalizer (proofIi_le D hNi)
    ((uc22p22e_jOf_le_self D.T).trans (D.sylowM.le.trans (uc22p22xf_hV D)))

theorem preN_le_M (D : Data G) (Y : Subgroup (MBar D.M D.U)) : preN D Y ≤ D.M :=
  inf_le_right.trans (Subgroup.map_subtype_le _)

theorem mem_preN (D : Data G) {Y : Subgroup (MBar D.M D.U)} {x : G} :
    x ∈ preN D Y ↔ x ∈ proofN D ∧ ∃ h : x ∈ D.M, (QuotientGroup.mk ⟨x, h⟩ : MBar D.M D.U) ∈ Y := by
  constructor
  · rintro ⟨hxN, z, hz, rfl⟩
    exact ⟨hxN, z.2, hz⟩
  · rintro ⟨hxN, h, hY⟩
    exact ⟨hxN, ⟨x, h⟩, hY, rfl⟩

theorem mbarImage_preN (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D)) : mbarImage D.M D.U (preN D Y) = Y := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ((mem_preN D).1 hz).2.choose_spec
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := hY ha
    exact ⟨z, (mem_preN D).2 ⟨hz, z.2, ha⟩, rfl⟩

theorem jOf_M_le_of_normalized (D : Data G) {R : Subgroup G} (hTR : jOf D.T ≤ R)
    (hR : ∀ n ∈ proofN D, ∀ r ∈ R, n * r * n⁻¹ ∈ R) : proofN D ≤ R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNM : proofN D ≤ D.M := uc22p22e_jOf_le_self D.M
  have hMN := uc22p22t_M_le_normalizer_jOf D
  have hTN : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ proofN D) (proofN D) :=
    D.sylowM.inf_of_le_normalizer hNM hMN
  have hFr := uc22p22t_frattini_sup hNM hMN hTN
  set Hn : Subgroup G := D.M ⊓ normalizer ((D.T ⊓ proofN D : Subgroup G) : Set G) with hHn
  have hHnN : Hn ≤ normalizer (proofN D : Set G) := inf_le_left.trans hMN
  refine jOf_le_of_forall_isMax (T := D.M) fun A₀ hA₀ x hx => ?_
  obtain ⟨hAM, hAel, hAmax⟩ := hA₀
  obtain ⟨k, hk, hkA⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf
    D.sylowM hAM (uc22p22e_isPGroup_of_elem hAel)
  have hA'T : A₀.map (MulAut.conj k⁻¹).toMonoidHom ≤ D.T := by
    rintro _ ⟨y, hy, rfl⟩
    have := hkA y hy
    simpa using this
  have hA'max : CFSG.Quasithin.IsMaxElemAbelian D.T (A₀.map (MulAut.conj k⁻¹).toMonoidHom) := by
    refine ⟨hA'T, uc22p22e_isElemAbelian_map hAel _, fun B hBT hBel => ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]
    exact hAmax B (hBT.trans D.sylowM.le) hBel
  have hxk : k⁻¹ * x * k ∈ jOf D.T := le_jOf_of_isMax hA'max ⟨x, hx, by simp⟩
  have hkmem : k ∈ (proofN D : Set G) * (Hn : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hHnN]
    exact hFr hk
  obtain ⟨n, hn, h, hh, rfl⟩ := hkmem
  have hhJ : ∀ y ∈ jOf D.T, h * y * h⁻¹ ∈ jOf D.T := by
    refine uc22p22e_conj_jOf (fun y hy => ?_)
    have hyTN : y ∈ D.T ⊓ proofN D :=
      ⟨uc22p22e_jOf_le_self D.T hy, uc22p22e_jOf_le D.sylowM hy⟩
    exact ((Subgroup.mem_normalizer_iff.1 hh.2 y).1 hyTN).1
  have h3 : n⁻¹ * x * n ∈ jOf D.T := by
    have := hhJ _ hxk
    have e : h * ((n * h)⁻¹ * x * (n * h)) * h⁻¹ = n⁻¹ * x * n := by group
    rwa [e] at this
  have := hR n hn _ (hTR h3)
  simpa [mul_assoc] using this

end Group

section Module

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.ne_bot (d : NatDec ρ Nbar Nb) (i : Fin m) : Nb i ≠ ⊥ := by
  obtain ⟨n, hn, F, _, _, hF, hinvA, hinvB, hBA, φ, ψ, hψB, hψA, hψs, hψφ⟩ := d.nat i
  intro h
  have h1 : Nat.card ↥(Nb i) = 1 := by rw [h]; exact Subgroup.card_bot
  have h2 : Nat.card ↥(Nb i) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv, card_statedSL_two]
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h3 : 6 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
    have h4 : 3 ≤ Nat.card F ^ 2 - 1 := by
      have : 4 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    exact Nat.mul_le_mul hq h4
  omega

end Module

section Claim3

theorem NatDec.exists_act_ne (D : Data G) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]
    {ρ : Representation (ZMod 2) (MBar D.M D.U) Umod} {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (d : NatDec ρ (mbarImage D.M D.U (proofN D)) Nb) (i : Fin m) :
    ∃ a ∈ mbarImage D.M D.U (jOf D.T), ∃ y ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i),
      ρ a y ≠ y := by
  by_contra hcon
  push Not at hcon
  let stabI : Subgroup (MBar D.M D.U) :=
    { carrier := {a | ∀ y ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i), ρ a y = y}
      mul_mem' := fun {a b} ha hb y hy => by
        rw [map_mul, Module.End.mul_apply, hb y hy, ha y hy]
      one_mem' := fun y _ => by simp
      inv_mem' := fun {a} ha y hy => by
        conv_lhs => rw [← ha y hy]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  set R : Subgroup G :=
    (stabI.comap (QuotientGroup.mk' (kerAct D.M D.U).normalCore)).map D.M.subtype with hRdef
  have hTR : jOf D.T ≤ R := fun x hx => by
    have hxM : x ∈ D.M := D.sylowM.le (uc22p22e_jOf_le_self D.T hx)
    exact ⟨⟨x, hxM⟩, hcon _ ⟨⟨x, hxM⟩, hx, rfl⟩, rfl⟩
  have hR : ∀ n ∈ proofN D, ∀ r ∈ R, n * r * n⁻¹ ∈ R := by
    rintro n hn _ ⟨z, hz, rfl⟩
    have hnM : n ∈ D.M := uc22p22e_jOf_le_self D.M hn
    have hnb : (QuotientGroup.mk' (kerAct D.M D.U).normalCore ⟨n, hnM⟩ : MBar D.M D.U) ∈
        mbarImage D.M D.U (proofN D) := ⟨⟨n, hnM⟩, hn, rfl⟩
    refine ⟨⟨n, hnM⟩ * z * ⟨n, hnM⟩⁻¹, ?_, by simp⟩
    show ∀ y ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i),
      ρ (QuotientGroup.mk' (kerAct D.M D.U).normalCore (⟨n, hnM⟩ * z * ⟨n, hnM⟩⁻¹)) y = y
    intro y hy
    set nb : MBar D.M D.U := QuotientGroup.mk' (kerAct D.M D.U).normalCore ⟨n, hnM⟩ with hnb_def
    have hy' : ρ nb⁻¹ y ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i) :=
      d.inv_Ii (Subgroup.inv_mem _ hnb) i y hy
    have hz' : ρ (QuotientGroup.mk' (kerAct D.M D.U).normalCore z) (ρ nb⁻¹ y) = ρ nb⁻¹ y :=
      hz _ hy'
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hz', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hNR := jOf_M_le_of_normalized D hTR hR
  apply d.ne_bot i
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨z, hz, rfl⟩ := d.le i hb
  obtain ⟨w, hw, hwz⟩ := hNR hz
  have : w = z := Subtype.ext hwz
  subst this
  exact Subgroup.mem_bot.2 (d.faithful i hb hw)

end Claim3

section EiHat

variable {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]

theorem bsub_proofIi (D : Data G) (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hc : ConjModule D.M D.U e ρ)
    {Y : Subgroup (MBar D.M D.U)} (hY : Y ≤ mbarImage D.M D.U (proofN D)) :
    bsub e (proofIi D (preN D Y)) = natIi ρ (mbarImage D.M D.U (proofN D)) Y := by
  have hV := uc22p22xf_hV D
  have hN : proofN D ≤ D.M := uc22p22e_jOf_le_self D.M
  obtain ⟨hle1, h1⟩ := bsub_commutator hV e ρ hc (W := D.U) (X := proofN D) le_rfl hN
  rw [bsub_V] at h1
  obtain ⟨hle2, h2⟩ := bsub_commutator hV e ρ hc (W := ⁅D.U, proofN D⁆) (X := preN D Y) hle1
    (preN_le_M D Y)
  unfold proofIi
  rw [h2, h1, mbarImage_preN D hY]
  rfl

theorem bsub_proofEiHat (D : Data G) (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hc : ConjModule D.M D.U e ρ)
    {Y : Subgroup (MBar D.M D.U)} (hY : Y ≤ mbarImage D.M D.U (proofN D)) :
    bsub e (proofEiHat D (preN D Y)) =
      commOn ρ (mbarImage D.M D.U (jOf D.T)) (natIi ρ (mbarImage D.M D.U (proofN D)) Y) := by
  have hV := uc22p22xf_hV D
  have hJM : jOf D.T ≤ D.M := (uc22p22e_jOf_le_self D.T).trans D.sylowM.le
  rw [← bsub_proofIi D e ρ hc hY]
  exact (bsub_commutator hV e ρ hc (W := proofIi D (preN D Y)) (X := jOf D.T)
    (proofIi_le D (preN_le_M D Y)) hJM).2

end EiHat

end P22x

open P22x

theorem uc22p22xg_proofEiHat_ne_bot (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m) :
    proofEiHat D (preN D (Nb i)) ≠ ⊥ ∧ proofEiHat D (preN D (Nb i)) ≤ D.U := by
  refine ⟨?_, proofEiHat_le D (preN_le_M D (Nb i))⟩
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  obtain ⟨a, ha, y, hy, hne⟩ := NatDec.exists_act_ne D d i
  intro hbot
  have hb := bsub_proofEiHat D e ρ hc (d.le i)
  rw [hbot, (bsub_eq_bot_iff e bot_le).2 rfl] at hb
  have hmem : ρ a y - y ∈ commOn ρ (mbarImage D.M D.U (jOf D.T))
      (natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i)) := sub_mem_commOn ha hy
  rw [← hb, Submodule.mem_bot] at hmem
  exact hne (sub_eq_zero.1 hmem)

theorem uc22p22xg_preN_le_centralizer (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) {i k : Fin m} (hik : k ≠ i) :
    preN D (Nb k) ≤ centralizer (proofEiHat D (preN D (Nb i)) : Set G) := by
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨-, hxM, hxb⟩ := (mem_preN D).1 hx
  have hzU : z ∈ D.U := proofEiHat_le D (preN_le_M D (Nb i)) hz
  obtain ⟨u, rfl⟩ := exists_iota e hzU
  have hu : u ∈ bsub e (proofEiHat D (preN D (Nb i))) := mem_bsub.2 hz
  rw [bsub_proofEiHat D e ρ hc (d.le i)] at hu
  have hQ : mbarImage D.M D.U (jOf D.T) ≤ mbarImage D.M D.U (proofN D) :=
    mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)
  have hu' : u ∈ natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i) :=
    commOn_le_of_invariant (fun a ha v hv => d.inv_Ii (hQ ha) i v hv) hu
  have h1 := d.lemma21 hik hxb hu'
  have h2' := iota_rho hV e ρ hc ⟨x, hxM⟩ u
  rw [h1] at h2'
  calc iota e u * x = (x * iota e u * x⁻¹) * x := by rw [← h2']
    _ = x * iota e u := by group

theorem uc22p22xg_cent_le_centralizer (D : Data G) {Ni : Subgroup G} (hNi : Ni ≤ D.M) :
    D.M ⊓ centralizer (D.U : Set G) ≤ centralizer (proofEiHat D Ni : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le (proofEiHat_le D hNi))

end CFSG.LocalAnalysis.UniquenessCase.UC22
