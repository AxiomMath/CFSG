module

public import CFSG.Quasithin.Vol2.Ch3E215MH
public import CFSG.Quasithin.Vol2.E2SevenKG6
public import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
public import CFSG.Quasithin.Background.AutOnFixV
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexDisplacement

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.B2F
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem thompsonReplacement {R S V A : Subgroup G} (hRS : R ≤ S) (hVR : V ≤ R)
    (hV : IsElemAbelian 2 V) (hA : IsMaxElemAbelian S A)
    (hcomm : ⁅V, A ⊓ R⁆ = ⊥) :
    (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ (V ⊓ A).relIndex V ∧
      (V ⊓ A).relIndex V ≤ (A ⊓ R).relIndex A ∧
      ((V ⊓ A).relIndex V = (A ⊓ R).relIndex A ↔
        IsMaxElemAbelian S (V ⊔ (A ⊓ R))) := by
  have hVS : V ≤ S := hVR.trans hRS
  have hAea : IsElemAbelian 2 A := hA.2.1
  have hRinfA_ea : IsElemAbelian 2 (A ⊓ R) := CFSG.Open.IsElemAbelian.mono hAea inf_le_left
  have hcomm' : ∀ v ∈ V, ∀ a ∈ A ⊓ R, v * a = a * v := by
    intro v hv a ha
    have h1 : ⁅v, a⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator hv ha
    rw [Subgroup.mem_bot] at h1
    have h2 : v * a = a * v := by
      have := congrArg (fun x : G => x * (a * v)) h1
      simpa [commutatorElement_def, mul_assoc] using this
    exact h2
  have hsup_ea : IsElemAbelian 2 (V ⊔ (A ⊓ R)) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hV hRinfA_ea hcomm'
  have hsupS : V ⊔ (A ⊓ R) ≤ S := sup_le hVS (inf_le_left.trans hA.1)
  have hsupA : Nat.card (V ⊔ (A ⊓ R) : Subgroup G) ≤ Nat.card A := hA.2.2 _ hsupS hsup_ea
  have hVCA : V ⊓ A ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    refine inf_le_inf_left V fun x hx => ?_
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => (CFSG.Open.IsElemAbelian.comm hAea hy hx)
  have h1 : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ (V ⊓ A).relIndex V :=
    Subgroup.relIndex_le_of_le_left hVCA (CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _)
  have hsupcard : Nat.card (V ⊔ (A ⊓ R) : Subgroup G) * Nat.card (V ⊓ (A ⊓ R) : Subgroup G) =
      Nat.card V * Nat.card (A ⊓ R : Subgroup G) :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V (A ⊓ R) hcomm').1
  have hinf : V ⊓ (A ⊓ R) = V ⊓ A := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxV, hxA, -⟩
      exact ⟨hxV, hxA⟩
    · rintro ⟨hxV, hxA⟩
      exact ⟨hxV, hxA, hVR hxV⟩
  have hVcard : (V ⊓ A).relIndex V * Nat.card (V ⊓ A : Subgroup G) = Nat.card V := by
    have := Subgroup.relIndex_mul_card (V ⊓ A) V
    rwa [inf_of_le_left inf_le_left] at this
  have hAcard : (A ⊓ R).relIndex A * Nat.card (A ⊓ R : Subgroup G) = Nat.card A := by
    have := Subgroup.relIndex_mul_card (A ⊓ R) A
    rwa [inf_of_le_left inf_le_left] at this
  have hxq : Nat.card (V ⊔ (A ⊓ R) : Subgroup G) =
      (V ⊓ A).relIndex V * Nat.card (A ⊓ R : Subgroup G) := by
    have hp : 0 < Nat.card (V ⊓ A : Subgroup G) := Nat.card_pos
    have h1 : Nat.card (V ⊔ (A ⊓ R) : Subgroup G) * Nat.card (V ⊓ A : Subgroup G) =
        ((V ⊓ A).relIndex V * Nat.card (A ⊓ R : Subgroup G)) *
          Nat.card (V ⊓ A : Subgroup G) := by
      calc Nat.card (V ⊔ (A ⊓ R) : Subgroup G) * Nat.card (V ⊓ A : Subgroup G)
          = Nat.card V * Nat.card (A ⊓ R : Subgroup G) := by
              rw [← hinf]; exact hsupcard
        _ = ((V ⊓ A).relIndex V * Nat.card (V ⊓ A : Subgroup G)) *
              Nat.card (A ⊓ R : Subgroup G) := by rw [hVcard]
        _ = ((V ⊓ A).relIndex V * Nat.card (A ⊓ R : Subgroup G)) *
              Nat.card (V ⊓ A : Subgroup G) := by ring
    exact Nat.eq_of_mul_eq_mul_right hp h1
  have h2 : (V ⊓ A).relIndex V ≤ (A ⊓ R).relIndex A := by
    have hle : (V ⊓ A).relIndex V * Nat.card (A ⊓ R : Subgroup G) ≤
        (A ⊓ R).relIndex A * Nat.card (A ⊓ R : Subgroup G) := by
      calc (V ⊓ A).relIndex V * Nat.card (A ⊓ R : Subgroup G)
          = Nat.card (V ⊔ (A ⊓ R) : Subgroup G) := hxq.symm
        _ ≤ Nat.card A := hsupA
        _ = (A ⊓ R).relIndex A * Nat.card (A ⊓ R : Subgroup G) := hAcard.symm
    exact Nat.le_of_mul_le_mul_right hle Nat.card_pos
  refine ⟨h1, h2, ?_⟩
  constructor
  · intro heq
    have hrA : Nat.card (V ⊔ (A ⊓ R) : Subgroup G) = Nat.card A := by
      rw [hxq, heq, hAcard]
    refine ⟨hsupS, hsup_ea, ?_⟩
    intro B hBS hBea
    rw [hrA]
    exact hA.2.2 B hBS hBea
  · intro hmax
    have hrA : Nat.card (V ⊔ (A ⊓ R) : Subgroup G) = Nat.card A :=
      le_antisymm hsupA (hmax.2.2 A hA.1 hAea)
    have heq : (V ⊓ A).relIndex V * Nat.card (A ⊓ R : Subgroup G) =
        (A ⊓ R).relIndex A * Nat.card (A ⊓ R : Subgroup G) := by
      rw [← hxq, hrA, hAcard]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos heq

theorem exists_le_autOn_eq {T V : Subgroup G}
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) {B : Subgroup (MulAut ↥V)}
    (hB : B ≤ autOn T V) :
    ∃ A : Subgroup G, A ≤ T ∧ autOn A V = B := by
  let ψ : T →* MulAut V := A4.actionOn V T hTV
  let C : Subgroup T := B.comap ψ
  refine ⟨C.map T.subtype, Subgroup.map_subtype_le C, ?_⟩
  have hAN : C.map T.subtype ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.map_subtype_le C |>.trans hTV
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := (A4.mem_autOn_iff hAN).mp hb
    obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp a.2
    have hψc : ψ c ∈ B := hc
    have hbc : b = ψ c := by
      rw [← ha]
      ext v
      rw [A4.actionOn_apply_coe, A4.actionOn_apply_coe]
      rw [← hca]
      rfl
    rw [hbc]
    exact hψc
  · intro hb
    obtain ⟨t, ht⟩ := (A4.mem_autOn_iff hTV).mp (hB hb)
    have htC : t ∈ C := by
      show ψ t ∈ B
      rw [show ψ t = b from ht]
      exact hb
    refine (A4.mem_autOn_iff hAN).mpr ⟨⟨t, ⟨t, htC, rfl⟩⟩, ?_⟩
    have hEq : (A4.actionOn V (C.map T.subtype) hAN) ⟨t, ⟨t, htC, rfl⟩⟩ = ψ t := by
      ext v
      rw [A4.actionOn_apply_coe, A4.actionOn_apply_coe]
    exact hEq.trans ht

theorem not_isFFInt_of_disp_sub {G₁ T V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hT : IsSylowTwoOf T G₁)
    (hdisp : ∀ A : Subgroup G, A ≤ T →
      (∀ a ∈ A, ∀ b ∈ A,
        a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
          a * a ∈ Subgroup.centralizer (V : Set G)) →
      ¬ A ≤ Subgroup.centralizer (V : Set G) →
      ∃ t ∈ A, t ∉ Subgroup.centralizer (V : Set G) ∧
        (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A <
          (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V) :
    ¬ IsFFInt G₁ V hV := by
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  intro hFF
  obtain ⟨Astar, hAstar_le, hAstar_ne, hAstar_el, hAstar_off⟩ := hFF
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hG₁V
  have hSyl : IsSylowTwoOf (autOn T V) (autOn G₁ V) := AutOn.isSylowTwoOf_autOn hT hG₁V
  have hAstarP : IsPGroup 2 Astar := hAstar_el.isPGroup
  obtain ⟨X, hX, hBX⟩ := exists_conj_le_of_isSylowTwoOf hSyl hAstar_le hAstarP
  set B : Subgroup (MulAut ↥V) := cjSub X Astar with hBdef
  have hB_el : IsElemAbelian2 B := B6.isElemAbelian2_conjSub hAstar_el X
  have hB_ne : B ≠ ⊥ := by
    intro hbot
    apply hAstar_ne
    have h1 : cjSub X⁻¹ (cjSub X Astar) = Astar := by
      simpa using cjSub_cjSub_inv X⁻¹ Astar
    have h2 : cjSub X⁻¹ (⊥ : Subgroup (MulAut ↥V)) = ⊥ := by
      rw [cjSub, Subgroup.map_bot]
    have := congrArg (cjSub X⁻¹) hbot
    rw [hBdef, h1, h2] at this
    exact this
  have hB_off : Nat.card ↥V ≤ Nat.card B * Nat.card (fixV B) := by
    rw [hBdef]
    change Nat.card ↥V ≤ Nat.card (Astar.map (MulAut.conj X).toMonoidHom) *
      Nat.card (fixV (Astar.map (MulAut.conj X).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj X).injective,
      CFSG.Quasithin.ConjTransport.card_fixV_map_conj]
    exact hAstar_off
  obtain ⟨A, hAT, haut⟩ := exists_le_autOn_eq hTN hBX
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hTN
  have hA_quad : ∀ a ∈ A, ∀ b ∈ A,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
        a * a ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha b hb
    have haN : a ∈ Subgroup.normalizer (V : Set G) := hAN ha
    have hbN : b ∈ Subgroup.normalizer (V : Set G) := hAN hb
    have hφa : conjAct V ⟨a, haN⟩ ∈ B := by
      rw [← haut]
      exact AutOn.conjAct_mem_autOn_of_mem haN ha
    have hφb : conjAct V ⟨b, hbN⟩ ∈ B := by
      rw [← haut]
      exact AutOn.conjAct_mem_autOn_of_mem hbN hb
    constructor
    · have hc : a * b * a⁻¹ * b⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
      have hN : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (V : Set G) := hAN hc
      have hsub : (⟨a * b * a⁻¹ * b⁻¹, hN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩⁻¹ :
            Subgroup.normalizer (V : Set G)) := Subtype.ext rfl
      have h1 : conjAct V ⟨a * b * a⁻¹ * b⁻¹, hN⟩ = 1 := by
        rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv]
        have hcomm := hB_el.1 _ hφa _ hφb
        calc (conjAct V ⟨a, haN⟩ * conjAct V ⟨b, hbN⟩) *
              (conjAct V ⟨a, haN⟩)⁻¹ * (conjAct V ⟨b, hbN⟩)⁻¹
            = ((conjAct V ⟨b, hbN⟩) * conjAct V ⟨a, haN⟩) *
              (conjAct V ⟨a, haN⟩)⁻¹ * (conjAct V ⟨b, hbN⟩)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      exact A4.conjAct_eq_one_iff.mp h1
    · have hc : a * a ∈ A := A.mul_mem ha ha
      have hN : a * a ∈ Subgroup.normalizer (V : Set G) := hAN hc
      have hsub : (⟨a * a, hN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨a, haN⟩ * ⟨a, haN⟩ : Subgroup.normalizer (V : Set G)) := Subtype.ext rfl
      have h1 : conjAct V ⟨a * a, hN⟩ = 1 := by
        rw [hsub, map_mul, ← pow_two, hB_el.2 _ hφa]
      exact A4.conjAct_eq_one_iff.mp h1
  have hAnc : ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hB_ne
    rw [← haut]
    exact AutOn.autOn_eq_bot_of_le_centralizer hle
  obtain ⟨t, htA, htnc, hlt⟩ := hdisp A hAT hA_quad hAnc
  have htN : t ∈ Subgroup.normalizer (V : Set G) := hAN htA
  have hCV : V ⊓ Subgroup.centralizer (A : Set G) ≤
      V ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine inf_le_inf_left V ?_
    exact Subgroup.centralizer_le (by rintro x rfl; exact htA)
  have hle1 : (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V :=
    Subgroup.relIndex_le_of_le_left hCV (CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _)
  have hcardA : Nat.card B = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    rw [← haut, AutOn.card_autOn_eq_relIndex hAN]
  have hcardFix : Nat.card (fixV B) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [← haut, AutOn.card_fixV_autOn_eq hAN]
  have hle2 : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ Nat.card B := by
    have h2 := Subgroup.relIndex_mul_card
      (V ⊓ Subgroup.centralizer (A : Set G)) V
    rw [inf_of_le_left (inf_le_left : V ⊓ Subgroup.centralizer (A : Set G) ≤ V)] at h2
    have hx : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
        Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ≤
        Nat.card B * Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
      calc (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
            Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)
          = Nat.card V := h2
        _ ≤ Nat.card B * Nat.card (fixV B) := hB_off
        _ = Nat.card B *
            Nat.card (V ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by rw [hcardFix]
    exact Nat.le_of_mul_le_mul_right hx Nat.card_pos
  have hle : (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V ≤
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    calc (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V
        ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := hle1
      _ ≤ Nat.card B := hle2
      _ = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := hcardA
  exact not_lt_of_ge hle hlt

theorem not_isDualFFInt_of_disp_sub {G₁ T V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hG₁V : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hT : IsSylowTwoOf T G₁)
    (hdisp : ∀ A : Subgroup G, A ≤ T →
      (∀ a ∈ A, ∀ b ∈ A,
        a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
          a * a ∈ Subgroup.centralizer (V : Set G)) →
      ¬ A ≤ Subgroup.centralizer (V : Set G) →
        (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A <
          Nat.card (⁅V, A⁆ : Subgroup G)) :
    ¬ IsDualFFInt G₁ V hV := by
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  intro hFF
  obtain ⟨B, hB_le, hB_ne, hB_el, hB_off⟩ := hFF
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hG₁V
  let δ : MulAut ↥V →* MulAut (DualGrp ↥V) := dualAct ↥V
  have hδinj : Function.Injective δ :=
    dualAct_injective (V := ↥V) (fun v : ↥V => Subtype.ext (hV.2 v v.2))
  let C : Subgroup (MulAut ↥V) := B.comap δ
  have hB_range : B ≤ δ.range := hB_le.trans (Subgroup.map_le_range δ (autOn G₁ V))
  have hB_eq : dualSub C = B := Subgroup.map_comap_eq_self hB_range
  have hC_le : C ≤ autOn G₁ V := by
    intro c hc
    obtain ⟨a, ha, hca⟩ := Subgroup.mem_map.mp (hB_le (show δ c ∈ B from hc))
    rw [← hδinj hca]
    exact ha
  have hC_el : IsElemAbelian2 C := by
    constructor
    · intro x hx y hy
      apply hδinj
      exact hB_el.1 _ hx _ hy
    · intro x hx
      apply hδinj
      exact hB_el.2 _ hx
  have hC_ne : C ≠ ⊥ := by
    intro hbot
    apply hB_ne
    rw [← hB_eq, hbot]
    exact Subgroup.map_bot δ
  have hSyl : IsSylowTwoOf (autOn T V) (autOn G₁ V) := AutOn.isSylowTwoOf_autOn hT hG₁V
  obtain ⟨X, hX, hCX⟩ := exists_conj_le_of_isSylowTwoOf hSyl hC_le hC_el.isPGroup
  set C' : Subgroup (MulAut ↥V) := cjSub X C with hC'def
  have hC'_le : C' ≤ autOn T V := hCX
  have hC'_el : IsElemAbelian2 C' := B6.isElemAbelian2_conjSub hC_el X
  obtain ⟨A, hAT, haut⟩ := exists_le_autOn_eq hTN hC'_le
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAT.trans hTN
  have hA_quad : ∀ a ∈ A, ∀ b ∈ A,
      a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (V : Set G) ∧
        a * a ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha b hb
    have haN : a ∈ Subgroup.normalizer (V : Set G) := hAN ha
    have hbN : b ∈ Subgroup.normalizer (V : Set G) := hAN hb
    have hφa : conjAct V ⟨a, haN⟩ ∈ C' := by
      rw [← haut]
      exact AutOn.conjAct_mem_autOn_of_mem haN ha
    have hφb : conjAct V ⟨b, hbN⟩ ∈ C' := by
      rw [← haut]
      exact AutOn.conjAct_mem_autOn_of_mem hbN hb
    constructor
    · have hc : a * b * a⁻¹ * b⁻¹ ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
      have hN : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.normalizer (V : Set G) := hAN hc
      have hsub : (⟨a * b * a⁻¹ * b⁻¹, hN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨a, haN⟩ * ⟨b, hbN⟩ * ⟨a, haN⟩⁻¹ * ⟨b, hbN⟩⁻¹ :
            Subgroup.normalizer (V : Set G)) := Subtype.ext rfl
      have h1 : conjAct V ⟨a * b * a⁻¹ * b⁻¹, hN⟩ = 1 := by
        rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv]
        have hcomm := hC'_el.1 _ hφa _ hφb
        calc (conjAct V ⟨a, haN⟩ * conjAct V ⟨b, hbN⟩) *
              (conjAct V ⟨a, haN⟩)⁻¹ * (conjAct V ⟨b, hbN⟩)⁻¹
            = ((conjAct V ⟨b, hbN⟩) * conjAct V ⟨a, haN⟩) *
              (conjAct V ⟨a, haN⟩)⁻¹ * (conjAct V ⟨b, hbN⟩)⁻¹ := by rw [hcomm]
          _ = 1 := by group
      exact A4.conjAct_eq_one_iff.mp h1
    · have hc : a * a ∈ A := A.mul_mem ha ha
      have hN : a * a ∈ Subgroup.normalizer (V : Set G) := hAN hc
      have hsub : (⟨a * a, hN⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨a, haN⟩ * ⟨a, haN⟩ : Subgroup.normalizer (V : Set G)) := Subtype.ext rfl
      have h1 : conjAct V ⟨a * a, hN⟩ = 1 := by
        rw [hsub, map_mul, ← pow_two, hC'_el.2 _ hφa]
      exact A4.conjAct_eq_one_iff.mp h1
  have hAnc : ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    have hbot : C' = ⊥ := by
      rw [← haut]
      exact AutOn.autOn_eq_bot_of_le_centralizer hle
    have hC_ne' : C ≠ ⊥ := hC_ne
    apply hC_ne'
    have h1 : cjSub X⁻¹ C' = C := by
      rw [hC'def]
      simpa using cjSub_cjSub_inv X⁻¹ C
    have h2 : cjSub X⁻¹ (⊥ : Subgroup (MulAut ↥V)) = ⊥ := by
      rw [cjSub, Subgroup.map_bot]
    have := congrArg (cjSub X⁻¹) hbot
    rw [h1, h2] at this
    exact this
  have hcardC' : Nat.card C' = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    rw [← haut, AutOn.card_autOn_eq_relIndex hAN]
  have hcardB : Nat.card B = Nat.card C' := by
    rw [← hB_eq]
    change Nat.card (C.map δ) = Nat.card C'
    rw [Subgroup.card_map_of_injective hδinj, card_cjSub X C]
  have hdualidx : (fixV B).index = Nat.card (commV C') := by
    rw [← hB_eq, index_fixV_dualSub (V := ↥V) (fun v : ↥V => Subtype.ext (hV.2 v v.2)) C,
      hC'def]
    exact (CFSG.Quasithin.ConjTransport.card_commV_map_conj C X).symm
  have hB_off' : Nat.card (fixV B) * (fixV B).index ≤
      Nat.card (fixV B) * Nat.card B := by
    have hcard : Nat.card (fixV B) * (fixV B).index = Nat.card (DualGrp ↥V) :=
      Subgroup.card_mul_index (fixV B)
    rw [hcard, mul_comm]
    exact hB_off
  have hcomm_le_B : Nat.card (commV C') ≤ Nat.card B := by
    rw [← hdualidx]
    exact Nat.le_of_mul_le_mul_left hB_off' Nat.card_pos
  have hltA := hdisp A hAT hA_quad hAnc
  have hcommA : Nat.card (commV C') = Nat.card (⁅V, A⁆ : Subgroup G) := by
    rw [← haut]
    have hmap := AutOn.map_commV_autOn_eq (X := A) (V := V) hAN
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (K := commV (autOn A V))
      (f := V.subtype) V.subtype_injective).symm
  have hle : Nat.card (⁅V, A⁆ : Subgroup G) ≤
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    calc Nat.card (⁅V, A⁆ : Subgroup G)
        = Nat.card (commV C') := hcommA.symm
      _ ≤ Nat.card B := hcomm_le_B
      _ = Nat.card C' := hcardB
      _ = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := hcardC'
  exact not_lt_of_ge hle hltA

theorem centralizerMod_eq_pCoreOf_of_isL2Quot {H U L N : Subgroup G} {m : ℕ}
    (hm2 : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) :
    centralizerMod L H N = pCoreOf 2 H := by
  classical
  have hsim : IsSimpleGroup (oTwoQuot ↥H) :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot hm2 hL2
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) :=
    CFSG.Quasithin.isElemAbelian_chiefMod hstep hUH hU
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hRleC : pCoreOf 2 H ≤ centralizerMod L H N :=
    Ch3z.pCoreOf_le_centralizerMod hUH hstep hE
  have hCnorm : H ≤ Subgroup.normalizer (centralizerMod L H N : Set G) :=
    CFSG.Quasithin.le_normalizer_centralizerMod hHL
      Subgroup.le_normalizer hHN
  set K := centralizerMod L H N with hKdef
  have hKH : K ≤ H := centralizerMod_le_left L H N
  by_cases hKHtop : K = H
  · exfalso
    apply hnc
    intro g hg x hx
    have hgK : g ∈ K := hKHtop ▸ hg
    exact hgK.2.2 x hx
  · refine le_antisymm ?_ hRleC
    let Kq : Subgroup (oTwoQuot ↥H) :=
      (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
    have hKnorm : (K.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (hKdef ▸ hCnorm)
    have hKqnorm : Kq.Normal :=
      Subgroup.Normal.map hKnorm _ (QuotientGroup.mk'_surjective _)
    have hKqne : Kq ≠ ⊤ := by
      intro htop
      apply hKHtop
      refine le_antisymm hKH ?_
      intro x hx
      have hmem : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) (⟨x, hx⟩ : ↥H) ∈ Kq := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
      have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
      have hdiff : (y : G)⁻¹ * x ∈ pCoreOf 2 H := by
        have h1 : (y⁻¹ * (⟨x, hx⟩ : ↥H) : ↥H) ∈ CFSG.Open.pCore 2 ↥H := by
          have hq : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
              (y⁻¹ * (⟨x, hx⟩ : ↥H)) = 1 := by
            rw [map_mul, map_inv, hyx, inv_mul_cancel]
          exact (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H)
            (x := y⁻¹ * (⟨x, hx⟩ : ↥H))).mp hq
        exact (CFSG.mem_openPCoreOf_iff (y⁻¹ * (⟨x, hx⟩ : ↥H))).mpr h1
      have hxeq : x = (y : G) * ((y : G)⁻¹ * x) := by group
      rw [hxeq]
      exact K.mul_mem hyK (hRleC hdiff)
    have hKqbot : Kq = ⊥ := by
      rcases (haveI := hKqnorm; IsSimpleGroup.eq_bot_or_eq_top_of_normal Kq) with hbot | htop
      · exact hbot
      · exact absurd htop hKqne
    intro k hk
    have hkH : k ∈ H := hKH hk
    let z : oTwoQuot ↥H :=
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) (⟨k, hkH⟩ : ↥H)
    have hzKq : z ∈ Kq :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
    rw [hKqbot] at hzKq
    have hz1 : z = 1 := Subgroup.mem_bot.mp hzKq
    have hkR : (⟨k, hkH⟩ : ↥H) ∈ CFSG.Open.pCore 2 ↥H :=
      (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H)
        (x := (⟨k, hkH⟩ : ↥H))).mp hz1
    exact (CFSG.mem_openPCoreOf_iff (⟨k, hkH⟩ : ↥H)).mpr hkR

theorem relIndex_inf_pCoreOf_le_two_pow {H A : Subgroup G} {m : ℕ}
    (hm2 : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hAH : A ≤ H) (hAe : IsElemAbelian 2 A) :
    (A ⊓ pCoreOf 2 H).relIndex A ≤ 2 ^ m := by
  classical
  have hm1 : 1 ≤ m := by omega
  let F := GaloisField 2 m
  obtain ⟨e₀⟩ := hL2
  let e : oTwoQuot ↥H ≃* SL(2, F) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := F))
  let φ : ↥H →* SL(2, F) := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
  have hker : φ.ker = CFSG.Open.pCore 2 ↥H := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) x = 1 := by
        apply e.injective
        rw [map_one]
        simpa [φ] using hx
      exact (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H) x).mp h1
    · intro hx
      have hq : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) x = 1 :=
        (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥H) x).mpr hx
      simp only [φ, MonoidHom.comp_apply, hq, map_one]
  have hsub : (pCoreOf 2 H).subgroupOf H = CFSG.Open.pCore 2 ↥H := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hrel : (CFSG.Open.pCore 2 ↥H).relIndex (A.subgroupOf H) =
      (A ⊓ pCoreOf 2 H).relIndex A := by
    rw [← hsub, Subgroup.relIndex_subgroupOf hAH,
      ← Subgroup.inf_relIndex_right (pCoreOf 2 H) A, inf_comm]
  have hcard := CFSG.Quasithin.Ch3E215M.card_map_eq_relIndex_ker φ (A.subgroupOf H)
  rw [hker, hrel] at hcard
  set B : Subgroup SL(2, F) := (A.subgroupOf H).map φ with hBdef
  have hBe : IsElemAbelian 2 B :=
    CFSG.Quasithin.Ch3E215M.isElemAbelian_map φ
      (CFSG.Open.IsElemAbelian.subgroupOf hAe H)
  have hBpg : IsPGroup 2 ↥B := hBe.isPGroup
  have hF : Nat.card F = 2 ^ m := GaloisField.card 2 m (by omega)
  have hT := CFSG.Quasithin.E2.isSylowTwoOf_sl2UpperUnipotentSubgroup (k := F) hm1 hF
  obtain ⟨h, -, hle⟩ :=
    CFSG.Quasithin.exists_conj_le_of_isSylowTwoOf hT (le_top : B ≤ ⊤) hBpg
  have hBcard : Nat.card B = Nat.card (cjSub h B) := (CFSG.Quasithin.card_cjSub _ _).symm
  calc (A ⊓ pCoreOf 2 H).relIndex A = Nat.card B := hcard
    _ = Nat.card (cjSub h B) := hBcard
    _ ≤ Nat.card (CFSG.GorensteinWalter.sl2UpperUnipotentSubgroup F) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card F := CFSG.Quasithin.E2.card_sl2UpperUnipotentSubgroup
    _ = 2 ^ m := hF

theorem l2_chiefStep_relIndex_ge {H V L N A : Subgroup G} {m : ℕ} (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hV : IsPGroup 2 ↥V) (hVH : V ≤ H)
    (hstep : IsChiefStep H V L N) (hnc : ¬ IsCentralStep H L N)
    (hAH : A ≤ H) (hA : IsElemAbelian 2 A)
    (hAnc : ¬ A ≤ centralizerMod L H N) :
    (A ⊓ pCoreOf 2 H).relIndex A ≤ (centralizerMod L N A).relIndex N := by
  have hCeq := centralizerMod_eq_pCoreOf_of_isL2Quot hm2 hL2 hV hVH hstep hnc
  obtain ⟨t, htA, htnc⟩ : ∃ t ∈ A, t ∉ centralizerMod L H N := by
    by_contra h
    push Not at h
    exact hAnc h
  have htH : t ∈ H := hAH htA
  have ht2 : t * t ∈ pCoreOf 2 H := by
    have hsq : t * t = 1 := by
      simpa [pow_two] using hA.2 t htA
    rw [hsq]
    exact (pCoreOf 2 H).one_mem
  have htO : t ∉ pCoreOf 2 H := by
    intro htR
    exact htnc (hCeq ▸ htR)
  have hq : 2 ^ m ≤ (centralizerMod L N (Subgroup.zpowers t)).relIndex N :=
    l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := m) hm2 hL2 hV hVH hstep hnc
      htH ht2 htO
  have hmono : centralizerMod L N A ≤ centralizerMod L N (Subgroup.zpowers t) :=
    centralizerMod_anti_right (V₁ := L) (X := N)
      (U := Subgroup.zpowers t) (U' := A) (Subgroup.zpowers_le.mpr htA)
  have hrel : (centralizerMod L N (Subgroup.zpowers t)).relIndex N ≤
      (centralizerMod L N A).relIndex N :=
    Subgroup.relIndex_le_of_le_left hmono (CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _)
  have himg : (A ⊓ pCoreOf 2 H).relIndex A ≤ 2 ^ m :=
    relIndex_inf_pCoreOf_le_two_pow hm2 hL2 hAH hA
  exact himg.trans (hq.trans hrel)

theorem exists_noncentral_chiefStep_of_one {H U N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) (hn : n = 1) :
    ∃ L K, IsChiefStep H U L K ∧ ¬ IsCentralStep H L K := by
  match n, h with
  | 0, .bot => omega
  | _, .central hstep hcent hser =>
      exact exists_noncentral_chiefStep_of_one hser hn
  | _, .noncentral hstep hnc _ => exact ⟨_, _, hstep, hnc⟩

theorem lemmaFF2_c_le_one {H V A : Subgroup G} {m c : ℕ} (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hV : IsElemAbelian 2 V) (hVH : V ≤ H)
    (hA : IsElemAbelian 2 A) (hAH : A ≤ H)
    (hAnR : ¬ A ≤ pCoreOf 2 H)
    (hbound : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
      (A ⊓ pCoreOf 2 H).relIndex A)
    (hser : IsChiefSeriesFrom H V V c) :
    c ≤ 1 := by
  classical
  have hVp : IsPGroup 2 ↥V := hV.isPGroup
  set k := (A ⊓ pCoreOf 2 H).relIndex A with hkdef
  have hkpos : k ≠ 0 := CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _
  have hkne : k ≠ 1 := by
    intro hk1
    apply hAnR
    intro a ha
    have hle : A ≤ A ⊓ pCoreOf 2 H := (Subgroup.relIndex_eq_one).mp hk1
    exact (Subgroup.mem_inf.mp (hle ha)).2
  have hk2 : 2 ≤ k := by omega
  have hk : ∀ L' N' : Subgroup G, IsChiefStep H V L' N' → ¬ IsCentralStep H L' N' →
      k ≤ (centralizerMod L' N' A).relIndex N' := by
    intro L' N' hstep' hnc'
    have hceq := centralizerMod_eq_pCoreOf_of_isL2Quot hm2 hL2 hVp hVH hstep' hnc'
    have hanc : ¬ A ≤ centralizerMod L' H N' := by
      rw [hceq]
      exact hAnR
    exact l2_chiefStep_relIndex_ge (m := m) hm2 hL2 hVp hVH hstep' hnc' hAH hA hanc
  have hpow := CFSG.Quasithin.D15Proof.pow_le_relIndex hVH hAH hk hser
  have hconv : (Subgroup.centralizer (A : Set G)).relIndex V =
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (A : Set G)) V, inf_comm]
  rw [hconv] at hpow
  by_cases hc0 : c = 0
  · omega
  · have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
    have hk_total : k ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := by
      have h1 : k ^ 1 ≤ k ^ c := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hkpos) hc1
      have h1' : k ≤ k ^ c := by simpa using h1
      exact h1'.trans hpow
    have htotal : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V = k :=
      le_antisymm hbound hk_total
    have hkc : k ^ c ≤ k := htotal ▸ hpow
    by_contra hc
    have hc2 : 2 ≤ c := by omega
    have h1 : k ^ 2 ≤ k ^ c := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hkpos) hc2
    have h2 : k * k ≤ k := by
      have := h1.trans hkc
      simpa [pow_two] using this
    nlinarith [hk2, h2]

theorem lemmaFF2_zero {H V : Subgroup G} (hV : IsElemAbelian 2 V)
    {c : ℕ} (hser : IsChiefSeriesFrom H V V c) (hc : c = 0) :
    ⁅V, oTwoUpper H⁆ = ⊥ :=
  CFSG.Quasithin.D14.commutator_eq_bot_of_zero hV.isPGroup hser hc

theorem lemmaFF2_one_numeric {H V A : Subgroup G} {m : ℕ} (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥H))
    (hV : IsElemAbelian 2 V) (hVH : V ≤ H)
    (hA : IsElemAbelian 2 A) (hAH : A ≤ H)
    (hAnR : ¬ A ≤ pCoreOf 2 H)
    (hbound : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
      (A ⊓ pCoreOf 2 H).relIndex A)
    (hser : IsChiefSeriesFrom H V V 1) :
    ∃ L N : Subgroup G, IsChiefStep H V L N ∧ ¬ IsCentralStep H L N ∧
      (A ⊓ pCoreOf 2 H).relIndex A = 2 ^ m ∧
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V = 2 ^ m ∧
      (centralizerMod L N A).relIndex N = 2 ^ m := by
  classical
  have hVp : IsPGroup 2 ↥V := hV.isPGroup
  obtain ⟨L, N, hstep, hnc⟩ := exists_noncentral_chiefStep_of_one hser rfl
  set k := (A ⊓ pCoreOf 2 H).relIndex A with hkdef
  have hkpos : k ≠ 0 := CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _
  have hkne : k ≠ 1 := by
    intro hk1
    apply hAnR
    intro a ha
    have hle : A ≤ A ⊓ pCoreOf 2 H := (Subgroup.relIndex_eq_one).mp hk1
    exact (Subgroup.mem_inf.mp (hle ha)).2
  have hk2 : 2 ≤ k := by omega
  have hk : ∀ L' N' : Subgroup G, IsChiefStep H V L' N' → ¬ IsCentralStep H L' N' →
      k ≤ (centralizerMod L' N' A).relIndex N' := by
    intro L' N' hstep' hnc'
    have hceq := centralizerMod_eq_pCoreOf_of_isL2Quot hm2 hL2 hVp hVH hstep' hnc'
    have hanc : ¬ A ≤ centralizerMod L' H N' := by
      rw [hceq]
      exact hAnR
    exact l2_chiefStep_relIndex_ge (m := m) hm2 hL2 hVp hVH hstep' hnc' hAH hA hanc
  have hk_le_step : k ≤ (centralizerMod L N A).relIndex N := hk L N hstep hnc
  have hpow := CFSG.Quasithin.D15Proof.pow_le_relIndex hVH hAH hk hser
  have hconv : (Subgroup.centralizer (A : Set G)).relIndex V =
      (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := by
    rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (A : Set G)) V, inf_comm]
  rw [hconv] at hpow
  have hk_total : k ≤ (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := by
    have h1 : k ^ 1 ≤ k ^ 1 := le_rfl
    simpa using hpow
  have htotal : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V = k :=
    le_antisymm hbound hk_total
  have hstep_le_total := CFSG.Quasithin.Ch3y.step_bound hVH hAH hk hstep hnc hser
  have hstep_le_k : (centralizerMod L N A).relIndex N ≤ k := by
    rw [hconv] at hstep_le_total
    have : k ^ (1 - 1) * (centralizerMod L N A).relIndex N ≤
        (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V := hstep_le_total
    rw [htotal] at this
    simpa using this
  have hstep_eq_k : (centralizerMod L N A).relIndex N = k := le_antisymm hstep_le_k hk_le_step
  have hCeq := centralizerMod_eq_pCoreOf_of_isL2Quot hm2 hL2 hVp hVH hstep hnc
  obtain ⟨t, htA, htnc⟩ : ∃ t ∈ A, t ∉ centralizerMod L H N := by
    by_contra h
    push Not at h
    exact (by rw [hCeq] at h; exact hAnR h)
  have htH : t ∈ H := hAH htA
  have ht2 : t * t ∈ pCoreOf 2 H := by
    have hsq : t * t = 1 := by simpa [pow_two] using hA.2 t htA
    rw [hsq]
    exact (pCoreOf 2 H).one_mem
  have htO : t ∉ pCoreOf 2 H := by
    intro htR
    exact htnc (hCeq ▸ htR)
  have hq : 2 ^ m ≤ (centralizerMod L N (Subgroup.zpowers t)).relIndex N :=
    l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := m) hm2 hL2 hVp hVH hstep hnc
      htH ht2 htO
  have hmono : centralizerMod L N A ≤ centralizerMod L N (Subgroup.zpowers t) :=
    centralizerMod_anti_right (V₁ := L) (X := N)
      (U := Subgroup.zpowers t) (U' := A) (Subgroup.zpowers_le.mpr htA)
  have hrel : (centralizerMod L N (Subgroup.zpowers t)).relIndex N ≤
      (centralizerMod L N A).relIndex N :=
    Subgroup.relIndex_le_of_le_left hmono (CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _)
  have hqk : 2 ^ m ≤ k := by
    rw [← hstep_eq_k]
    exact hq.trans hrel
  have himg : k ≤ 2 ^ m := relIndex_inf_pCoreOf_le_two_pow hm2 hL2 hAH hA
  have hkq : k = 2 ^ m := le_antisymm himg hqk
  exact ⟨L, N, hstep, hnc, hkq, htotal.trans hkq, hstep_eq_k.trans hkq⟩

end CFSG.Quasithin.Stroth
