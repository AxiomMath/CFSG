module

public import CFSG.Quasithin.Background.Harris.R1.QbetaKer
public import CFSG.Quasithin.Background.Harris.R1.QbetaData
public import CFSG.Quasithin.Recognition.SzR1CaseTwo

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7
  CFSG.Quasithin.F112W
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem card_eq_four_of_lt_le' {V Z W : Subgroup G} (hZV : Z ≤ V) (hne : V ≠ Z)
    (hVW : V ≤ W) (hZ : Nat.card ↥Z = 2) (hW : Nat.card ↥W = 4) : Nat.card ↥V = 4 := by
  have hd : Nat.card ↥V ∣ 4 := hW ▸ Subgroup.card_dvd_of_le hVW
  have hgt : 2 < Nat.card ↥V := by
    by_contra hcon
    refine hne (Subgroup.eq_of_le_of_card_ge hZV ?_).symm
    rw [hZ]
    omega
  have hle4 : Nat.card ↥V ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  generalize Nat.card ↥V = d at hd hgt hle4 ⊢
  interval_cases d <;> omega

theorem qd_of_famCtx_gen [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hΩ : 4 ≤ Fintype.card Ω) (hodd : Odd (Fintype.card Ω)) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀)
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs) :
    ∃ g y z : G, QD (L2 ⊔ S) S (pCoreOf 2 (L2 ⊔ S)) (vBeta K1 L2 S Zs) Zs (C.kerM ⊓ S)
      (C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G)) g y z ∧
      Nat.card ↥(Zs ⊔ conjSub g Zs) = 4 := by
  classical
  have hyp := C.amalgamHypV
  have hS := C.isNaturalS3
  have hSP : S ≤ L2 ⊔ S := le_sup_right
  have hQS : pCoreOf 2 (L2 ⊔ S) ≤ S := C.pCore_le_S
  have hQN : L2 ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 (L2 ⊔ S) : Set G) :=
    le_normalizer_pCoreOf 2 (L2 ⊔ S)
  have hS2 : IsPGroup 2 S := hyp.sylow₁.2.1
  have hmax : ∀ N : Subgroup G, N ≤ L2 ⊔ S → L2 ⊔ S ≤ Subgroup.normalizer (N : Set G) →
      IsPGroup 2 N → N ≤ pCoreOf 2 (L2 ⊔ S) :=
    fun N hNP hPN hN2 => le_pCoreOf_of_le_normalizer 2 hNP hPN hN2
  have hS3 : S.relIndex (L2 ⊔ S) = 3 := F112J2.relIndex_L2S C.hR C.h.s3
  have hQ2 : (pCoreOf 2 (L2 ⊔ S)).relIndex S = 2 := relIndex_pCoreOf_T hyp hS
  have hZW : ∀ g ∈ L2 ⊔ S, conjSub g Zs ≤ vBeta K1 L2 S Zs := fun g hg =>
    calc conjSub g Zs ≤ conjSub g (conjClosure Zs L2) := conjSub_mono g (le_conjClosure Zs L2)
      _ = conjClosure Zs L2 := F7.conjSub_eq_of_mem_normalizer (hyp.normalizes hg)
      _ ≤ vBeta K1 L2 S Zs := le_conjClosure (conjClosure Zs L2) (K1 ⊔ S)
  have hSM : S ≤ Subgroup.normalizer ((C.kerM ⊓ S : Subgroup G) : Set G) :=
    F7.le_normalizer_inf (le_sup_right.trans C.sup_le_normalizer_kerM) Subgroup.le_normalizer
  have hWM : vBeta K1 L2 S Zs ≤ C.kerM ⊓ S := le_inf C.vBeta_le_kerM C.vBeta_le_S
  have hMW : ⁅C.kerM ⊓ S, vBeta K1 L2 S Zs⁆ ≤ Zs :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans C.commutator_kerM_vBeta_le
  have hWQ : ¬ vBeta K1 L2 S Zs ≤ pCoreOf 2 (L2 ⊔ S) := C.not_vBeta_le_pCore hΩ
  have hnonab := C.commutator_vBeta_inf_pCore_ne_bot hΩ hij
  have hB1 : ∀ s ∈ pCoreOf 2 (L2 ⊔ S),
      (∀ w ∈ vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S), s * w * s⁻¹ * w⁻¹ ∈ Zs) → s ∈ C.kerM ⊓ S :=
    fun s hs hfix => ⟨C.mem_kerM_of_mem_pCore hΩ hij hs hfix, hQS hs⟩
  have vh : Vert.Hyp (L2 ⊔ S) S (pCoreOf 2 (L2 ⊔ S)) (vBeta K1 L2 S Zs) Zs (C.kerM ⊓ S) :=
    ⟨hSP, hQS, hQN, hS3, hQ2, C.vBeta_le_S, S_le_normalizer_vBeta K1 L2 S Zs, hSM, hWM, hZW,
      C.hcomm.le, hMW, hWQ, hnonab, hB1⟩
  obtain ⟨g, b, y, hgP, hgS, hgg, hbP, hbS, hbg, hyg, hyS, -⟩ :=
    Vert.exists_vertex_elements hSP hQS hQN hS2 hmax hS3 hQ2
  have hSZN : S ≤ Subgroup.normalizer (Zs : Set G) :=
    (F112J2.S_le_centralizer_Z C.h).trans (Subgroup.centralizer_le_normalizer (Zs : Set G))
  have hZP : ¬ L2 ⊔ S ≤ Subgroup.normalizer (Zs : Set G) := fun h =>
    C.h.Z_not_norm (le_sup_left.trans h)
  have hgZ : g ∉ Subgroup.normalizer (Zs : Set G) :=
    Vert.not_mem_normalizer_of_not_mem hSP hS3 hSZN hZP hgP hgS
  have hZZ : Zs ⊓ conjSub g Zs = ⊥ :=
    Vert.inf_eq_bot_of_card_two C.h.card_Z ((Vert.card_conjSub g Zs).trans C.h.card_Z)
      (fun h => hgZ (Vert.mem_normalizer_of_conjSub_eq h))
  have hz1 : C.cm i₀ j₀ ≠ 1 := C.cm_ne_one hij
  have hVle : Zs ⊔ conjSub g Zs ≤ conjClosure Zs L2 := by
    refine sup_le (le_conjClosure Zs L2) ?_
    calc conjSub g Zs ≤ conjSub g (conjClosure Zs L2) := conjSub_mono g (le_conjClosure Zs L2)
      _ = conjClosure Zs L2 := F7.conjSub_eq_of_mem_normalizer (hyp.normalizes hgP)
  have h4 : Nat.card ↥(Zs ⊔ conjSub g Zs) = 4 := by
    have hne : Zs ⊔ conjSub g Zs ≠ Zs := by
      intro h
      have hzg : conjSub g Zs ≤ Zs := le_sup_right.trans h.le
      have hz' : g * C.cm i₀ j₀ * g⁻¹ ∈ Zs ⊓ conjSub g Zs :=
        ⟨hzg (mul_mem_conjSub (C.cm_mem i₀ j₀)), mul_mem_conjSub (C.cm_mem i₀ j₀)⟩
      rw [hZZ, Subgroup.mem_bot] at hz'
      apply hz1
      have : C.cm i₀ j₀ = g⁻¹ * (g * C.cm i₀ j₀ * g⁻¹) * g := by group
      rw [this, hz']
      group
    exact card_eq_four_of_lt_le' le_sup_left hne hVle C.h.card_Z C.h.V_card
  have hVeq : Zs ⊔ conjSub g Zs = conjClosure Zs L2 :=
    Subgroup.eq_of_le_of_card_ge hVle (by rw [h4, C.h.V_card])
  refine ⟨g, y, C.cm i₀ j₀, ?_, h4⟩
  refine
    { vh := vh
      hS2 := hS2
      hMS := inf_le_right
      hg := hgP
      hyg := hyg
      hyS := hyS
      hgg := hgg
      hzZ := C.cm_mem i₀ j₀
      hz1 := hz1
      hZcases := fun x hx => Zs_eq_one_or C hij hx
      hZZ := hZZ
      hSZ := F112J2.S_le_centralizer_Z C.h
      hsqW := fun w hw => C.sq_mem_Zs hij hw
      hVab := ?_
      hVN := ?_
      hQV := ?_
      hVQ := ?_
      hZS := hZS
      hD := ?_
      hDc := ?_
      hDW := ?_
      hDS := ?_
      hMWD := ?_ }
  · intro a ha b hb
    rw [hVeq] at ha hb
    exact C.V_comm ha hb
  · rw [hVeq]
    exact hyp.normalizes
  · intro s hs hv
    rw [C.mem_pCore_iff]
    refine ⟨hs, fun v hv' => ?_⟩
    rw [← hVeq] at hv'
    exact (hv v hv').symm
  · intro v hv q hq
    rw [hVeq] at hv
    exact ((C.mem_pCore_iff.mp hq).2 v hv).symm
  · exact inf_le_left
  · intro d hd w hw
    exact (Subgroup.mem_centralizer_iff.mp hd.2 w hw).symm
  · intro x hx
    refine hcen x hx.2 (fun u hu => ?_)
    exact (Subgroup.mem_centralizer_iff.mp hx.1.2 u hu).symm
  · intro s hs
    have h1 : s ∈ Subgroup.normalizer ((C.kerM ⊓ S : Subgroup G) : Set G) := hSM hs
    have h2 : s ∈ Subgroup.normalizer
        ((Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) : Subgroup G) : Set G) := by
      have hW : conjSub s (vBeta K1 L2 S Zs) = vBeta K1 L2 S Zs :=
        F7.conjSub_eq_of_mem_normalizer (S_le_normalizer_vBeta K1 L2 S Zs hs)
      apply Vert.mem_normalizer_of_conjSub_eq
      rw [← conjSub_centralizer, hW]
    exact F7.mem_normalizer_inf h1 h2
  · intro m hm
    obtain ⟨w, hw, hwc⟩ := exists_inner_of_kerM C hodd hij l₀ hl₀ hall hcen hm.1
    exact ⟨w, hw, w⁻¹ * m,
      ⟨(C.kerM ⊓ S).mul_mem ((C.kerM ⊓ S).inv_mem (hWM hw)) hm, hwc⟩, by group⟩

theorem qd_of_famCtx [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hc5 : Fintype.card Ω = 5) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀)
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs) :
    ∃ g y z : G, QD (L2 ⊔ S) S (pCoreOf 2 (L2 ⊔ S)) (vBeta K1 L2 S Zs) Zs (C.kerM ⊓ S)
      (C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G)) g y z ∧
      Nat.card ↥(Zs ⊔ conjSub g Zs) = 4 :=
  qd_of_famCtx_gen C (by omega) ⟨2, by omega⟩ hij l₀ hl₀ hall hcen hZS

end CFSG.Quasithin.Background.Harris.R1
