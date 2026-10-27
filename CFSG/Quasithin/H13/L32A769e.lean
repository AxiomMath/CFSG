module

public import CFSG.Quasithin.H13.L32A767b
public import CFSG.Quasithin.H13.L32A767a
public import CFSG.Quasithin.H13.L32A769b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {x x' y : G}

@[expose] def IsF1 (T V : Subgroup G) (x f : G) : Prop :=
  ∃ w ∈ conjSub x (fsuU T V), w ∉ pCoreOf 2 (hz T V) ∧
    ∃ u ∈ fsuU T V, u ∉ V ⊔ u0 T V ∧ f = u * w * u⁻¹ * w⁻¹

namespace Conf69

variable (C : Conf69 G T L V x)
include C

theorem comm_QH {q u : G} (hq : q ∈ pCoreOf 2 (hz T V)) (hu : u ∈ fsuU T V) :
    q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have hqC : q ∈ centralizerMod (fsuV1 T V) (hz T V) (conjClosure V (hz T V)) := by
    rw [← C.hF.pCoreOf_eq_centralizerMod]
    exact hq
  exact hqC.2.2 u (fsuU_eq_conjClosure_hz C.hMod C.hyp ▸ hu)

theorem W_le_hz : conjSub x (fsuU T V) ≤ hz T V :=
  C.le_R1.trans ((pCoreOf_le_of_le C.hyp le_sup_right).trans C.hF.T_le_H)

theorem inf_V1_eq_bot' (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V)) :
    (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ fsuV1 T V = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  by_contra hv1
  apply hV1
  have hne : fsuV1 T V ⊓ conjSub x (fsuU T V) ≠ ⊥ := by
    intro hb
    have : v ∈ fsuV1 T V ⊓ conjSub x (fsuU T V) := ⟨hv.2, hv.1.2⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hv1 this
  exact le_of_card_eq_two_of_inf_ne_bot C.hF.card_V₁ hne

theorem isF1_of_mem (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V)) {f : G}
    (hf : f ∈ fsuU T V ⊓ conjSub x (fsuU T V)) {s : G}
    (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hsQ : s ∉ pCoreOf 2 (hz T V)) {u : G}
    (hu : u ∈ fsuU T V) (hfu : f * (u * s * u⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V) :
    f = 1 ∨ IsF1 T V x f := by
  have hWN : conjSub x (fsuU T V) ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    C.W_le_hz.trans (le_normalizer_pCoreOf 2 _)
  have hs' := hs
  rw [← C.sup_eq, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hWN] at hs'
  obtain ⟨w, hw, q, hq, rfl⟩ := hs'
  have hwQ : w ∉ pCoreOf 2 (hz T V) := fun h' => hsQ (mul_mem h' hq)
  have hwH : w ∈ hz T V := C.W_le_hz hw
  set c := u * w * u⁻¹ * w⁻¹ with hc
  have hcF : c ∈ fsuU T V ⊓ conjSub x (fsuU T V) :=
    C.comm_le (Subgroup.commutator_mem_commutator hu hw)
  have hd : u * q * u⁻¹ * q⁻¹ ∈ fsuV1 T V := by
    have := inv_mem (C.comm_QH hq hu)
    rwa [show (q * u * q⁻¹ * u⁻¹)⁻¹ = u * q * u⁻¹ * q⁻¹ by group] at this
  set d := w * (u * q * u⁻¹ * q⁻¹) * w⁻¹ with hd'
  have hdV : d ∈ fsuV1 T V := (Subgroup.mem_normalizer_iff.mp (C.hF.H_normalizes_V₁ hwH) _).mp hd
  have he : u * (w * q) * u⁻¹ * (w * q)⁻¹ = c * d := by
    rw [hc, hd']; group
  rw [he] at hfu
  have hdc : d * c = c * d :=
    (Subgroup.mem_centralizer_iff.mp
      ((C.hF.H_le_centralizer) (C.W_le_hz hcF.2)) d hdV)
  have hfc : f * c⁻¹ ∈ fsuV1 T V := by
    rw [show f * c⁻¹ = f * (c * d)⁻¹ * d by
      calc f * c⁻¹ = f * c⁻¹ * d⁻¹ * d := by group
        _ = f * (d * c)⁻¹ * d := by group
        _ = f * (c * d)⁻¹ * d := by rw [hdc]]
    exact mul_mem hfu hdV
  have hfc' : f * c⁻¹ ∈ (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ fsuV1 T V :=
    Subgroup.mem_inf.mpr ⟨mul_mem hf (inv_mem hcF), hfc⟩
  rw [C.inf_V1_eq_bot' hV1, Subgroup.mem_bot] at hfc'
  have hfeq : f = c := by
    calc f = f * c⁻¹ * c := by group
      _ = c := by rw [hfc', one_mul]
  by_cases huV : u ∈ V ⊔ u0 T V
  · left
    rw [hfeq, hc]
    have huc : u ∈ fsuU T V ⊓ Subgroup.centralizer (conjSub x (fsuU T V) : Set G) := by
      rw [C.cent.1]; exact huV
    rw [← Subgroup.mem_centralizer_iff.mp huc.2 w hw, mul_inv_cancel_right, mul_inv_cancel]
  · exact Or.inr ⟨w, hw, hwQ, u, hu, huV, hfeq⟩

theorem isF1_mem {f : G} (hf : IsF1 T V x f) :
    f ∈ fsuU T V ⊓ conjSub x (fsuU T V) ∧ f ∉ fsuV1 T V := by
  obtain ⟨w, hw, hwQ, u, hu, huV, rfl⟩ := hf
  refine ⟨C.comm_le (Subgroup.commutator_mem_commutator hu hw), fun h1 => huV ?_⟩
  refine mem_sup_u0_of_comm_mem C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334
    (C.le_R1 hw) hwQ hu ?_
  have := inv_mem h1
  rwa [show (u * w * u⁻¹ * w⁻¹)⁻¹ = w * u * w⁻¹ * u⁻¹ by group] at this

theorem F_le (f : G) (hf : f ∈ fsuU T V ⊓ conjSub x (fsuU T V)) : f ∈ V ⊔ u0 T V := by
  have : f ∈ (fsuU T V ⊓ conjSub x (fsuU T V)) ⊔ fsuV1 T V := Subgroup.mem_sup_left hf
  rwa [C.cent.2.2] at this

theorem partition_eight (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V))
    (h8 : Nat.card ↥(u0 T V) = 8) {f : G} (hf : f ∈ fsuU T V ⊓ conjSub x (fsuU T V)) :
    f ∈ V ∨ f ∈ u0 T V ∨ IsF1 T V x f := by
  rcases ((C.h64 G T L V C.hyp).2.2.2.1 h8).2 f (C.F_le f hf) with h | h |
    ⟨s, hs, hsQ, u, hu, hfu⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases C.isF1_of_mem hV1 hf hs hsQ hu hfu with h1 | h1
    · exact Or.inl (h1 ▸ one_mem V)
    · exact Or.inr (Or.inr h1)

theorem isF1_not_mem_V (h8 : Nat.card ↥(u0 T V) = 8) {f : G} (hf : IsF1 T V x f) : f ∉ V := by
  intro hfV
  obtain ⟨-, hf1⟩ := C.isF1_mem hf
  obtain ⟨w, hw, hwQ, u, hu, -, rfl⟩ := hf
  exact hf1 (((C.h64 G T L V C.hyp).2.2.2.1 h8).1 w (C.le_R1 hw) hwQ u hu hfV)

theorem partition_four (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V))
    (h4 : Nat.card ↥(u0 T V) = 4) {f : G} (hf : f ∈ fsuU T V ⊓ conjSub x (fsuU T V)) :
    f ∈ u0 T V ∨ IsF1 T V x f := by
  rcases ((C.h64 G T L V C.hyp).2.2.2.2 h4).2 f (C.F_le f hf) with h |
    ⟨s, hs, hsQ, u, hu, hfu⟩
  · exact Or.inl h
  · rcases C.isF1_of_mem hV1 hf hs hsQ hu hfu with h1 | h1
    · exact Or.inl (h1 ▸ one_mem _)
    · exact Or.inr h1

theorem isF1_not_mem_u0 {f : G} (hf : IsF1 T V x f) : f ∉ u0 T V := by
  intro hfU
  obtain ⟨-, hf1⟩ := C.isF1_mem hf
  obtain ⟨w, hw, hwQ, u, hu, -, rfl⟩ := hf
  exact hf1 ((C.h64 G T L V C.hyp).2.1 w (C.le_R1 hw) hwQ u hu hfU)

end Conf69

namespace Sym69

variable (S : Sym69 G T L V x x' y)
include S

theorem conj_inv_U : conjSub y⁻¹ (fsuU T V) = conjSub x' (fsuU T V) := by
  have := congrArg (conjSub y⁻¹) S.hW
  rw [conjSub_conjSub_inv] at this
  exact this.symm

theorem conj_inv_W : conjSub y⁻¹ (conjSub x (fsuU T V)) = fsuU T V := by
  rw [← S.hU, conjSub_conjSub_inv]

theorem conj_Q : conjSub y (pCoreOf 2 (hz T V)) = conjSub x (pCoreOf 2 (hz T V)) := by
  rw [← pCoreOf_conjSub, S.hH, pCoreOf_conjSub]

theorem conj_Q' : conjSub y (conjSub x' (pCoreOf 2 (hz T V))) = pCoreOf 2 (hz T V) := by
  rw [← pCoreOf_conjSub, ← pCoreOf_conjSub, S.hH']

theorem W_inf_Q : conjSub x (fsuU T V) ⊓ pCoreOf 2 (hz T V) = conjSub y (V ⊔ u0 T V) := by
  rw [← S.c'.inf_QW, conjSub_inf, S.hU, S.conj_Q']

theorem isF1_of_conj {f : G} (hf : IsF1 T V x' (y⁻¹ * f * y)) : IsF1 T V x f := by
  obtain ⟨w', hw', hw'Q, u, hu, huV, he⟩ := hf
  have hu'' : y * w' * y⁻¹ ∈ fsuU T V := by rw [← S.hW]; exact mul_mem_conjSub hw'
  have hw'' : y * u * y⁻¹ ∈ conjSub x (fsuU T V) := by rw [← S.hU]; exact mul_mem_conjSub hu
  have hu''V : y * w' * y⁻¹ ∉ V ⊔ u0 T V := by
    intro hm
    rw [← S.c.inf_QW] at hm
    apply hw'Q
    have h1 := (Subgroup.mem_inf.mp hm).2
    rw [← S.conj_Q, mem_conjSub] at h1
    rwa [show y⁻¹ * (y * w' * y⁻¹) * y = w' by group] at h1
  have hw''Q : y * u * y⁻¹ ∉ pCoreOf 2 (hz T V) := by
    intro hm
    have h1 : y * u * y⁻¹ ∈ conjSub x (fsuU T V) ⊓ pCoreOf 2 (hz T V) := ⟨hw'', hm⟩
    rw [S.W_inf_Q, mem_conjSub] at h1
    apply huV
    rwa [show y⁻¹ * (y * u * y⁻¹) * y = u by group] at h1
  refine ⟨y * u * y⁻¹, hw'', hw''Q, y * w' * y⁻¹, hu'', hu''V, ?_⟩
  have hfe : f = (y * u * y⁻¹) * (y * w' * y⁻¹) * (y * u * y⁻¹)⁻¹ * (y * w' * y⁻¹)⁻¹ := by
    rw [show f = y * (y⁻¹ * f * y) * y⁻¹ by group, he]
    group
  have hfU : f ∈ fsuU T V := by
    have h1 := S.c.comm_le (Subgroup.commutator_mem_commutator hu'' hw'')
    have h2 := inv_mem (Subgroup.mem_inf.mp h1).1
    rw [commutatorElement_def] at h2
    rw [hfe]
    convert h2 using 1
    group
  have hf2 : f * f = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one (isElemAbelian_fsuU_of S.c.hyp S.c.hMod) hfU
  calc f = f⁻¹ := (eq_inv_of_mul_eq_one_left hf2)
    _ = _ := by rw [hfe]; group

theorem partition_eight' (hV1' : ¬ fsuV1 T V ≤ conjSub x' (fsuU T V))
    (h8 : Nat.card ↥(u0 T V) = 8) {f : G} (hf : f ∈ fsuU T V ⊓ conjSub x (fsuU T V)) :
    f ∈ conjSub y V ∨ f ∈ conjSub y (u0 T V) ∨ IsF1 T V x f := by
  have hf' : y⁻¹ * f * y ∈ fsuU T V ⊓ conjSub x' (fsuU T V) := by
    have h1 : y⁻¹ * f * y ∈ conjSub y⁻¹ (conjSub x (fsuU T V)) ⊓ conjSub y⁻¹ (fsuU T V) := by
      have e : y⁻¹⁻¹ * (y⁻¹ * f * y) * y⁻¹ = f := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_conjSub, e]; exact (Subgroup.mem_inf.mp hf).2
      · rw [mem_conjSub, e]; exact (Subgroup.mem_inf.mp hf).1
    rw [S.conj_inv_W, S.conj_inv_U] at h1
    exact h1
  rcases S.c'.partition_eight hV1' h8 hf' with h | h | h
  · left; rw [mem_conjSub]; exact h
  · right; left; rw [mem_conjSub]; exact h
  · right; right; exact S.isF1_of_conj h

theorem partition_four' (hV1' : ¬ fsuV1 T V ≤ conjSub x' (fsuU T V))
    (h4 : Nat.card ↥(u0 T V) = 4) {f : G} (hf : f ∈ fsuU T V ⊓ conjSub x (fsuU T V)) :
    f ∈ conjSub y (u0 T V) ∨ IsF1 T V x f := by
  have hf' : y⁻¹ * f * y ∈ fsuU T V ⊓ conjSub x' (fsuU T V) := by
    have h1 : y⁻¹ * f * y ∈ conjSub y⁻¹ (conjSub x (fsuU T V)) ⊓ conjSub y⁻¹ (fsuU T V) := by
      have e : y⁻¹⁻¹ * (y⁻¹ * f * y) * y⁻¹ = f := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_conjSub, e]; exact (Subgroup.mem_inf.mp hf).2
      · rw [mem_conjSub, e]; exact (Subgroup.mem_inf.mp hf).1
    rw [S.conj_inv_W, S.conj_inv_U] at h1
    exact h1
  rcases S.c'.partition_four hV1' h4 hf' with h | h
  · left; rw [mem_conjSub]; exact h
  · right; exact S.isF1_of_conj h

theorem card_inf_F (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V)) {X : Subgroup G}
    (hV1X : fsuV1 T V ≤ X) (hX : X ≤ V ⊔ u0 T V) :
    Nat.card ↥((fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ X) * 2 = Nat.card ↥X := by
  have C := S.c
  have hUN : fsuU T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [fsuU_eq_conjClosure_hz C.hMod C.hyp]
    exact C.hF.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 _).trans C.hF.H_normalizes_V₁)
  have hN : (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ X ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    inf_le_left.trans (inf_le_left.trans hUN)
  have hsup : (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ X ⊔ fsuV1 T V = X := by
    refine le_antisymm (sup_le inf_le_right hV1X) fun v hv => ?_
    have hv' : v ∈ (fsuU T V ⊓ conjSub x (fsuU T V)) ⊔ fsuV1 T V := by
      rw [C.cent.2.2]; exact hX hv
    have hFN : fsuU T V ⊓ conjSub x (fsuU T V) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
      inf_le_left.trans hUN
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hFN] at hv'
    obtain ⟨f, hf, z, hz, rfl⟩ := hv'
    refine Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hf, ?_⟩) hz
    rw [show f = f * z * z⁻¹ by group]
    exact mul_mem hv (inv_mem (hV1X hz))
  have hinf : (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ X ⊓ fsuV1 T V = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ fsuV1 T V := ⟨hv.1.1, hv.2⟩
    rw [C.inf_V1_eq_bot' hV1] at this
    exact this
  have h1 := L32NSet14.card_sup_mul_card_inf hN
  rw [hsup, hinf, Subgroup.card_bot, C.hF.card_V₁] at h1
  omega

theorem false_of_card_u0_eight (h68 : Lemma14_7_68) (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V))
    (hV1' : ¬ fsuV1 T V ≤ conjSub x' (fsuU T V)) (h8 : Nat.card ↥(u0 T V) = 8) : False := by
  have C := S.c
  have h := C.hyp
  have h13322 := stmt13_3_2_two_of C.h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 C.h1222 C.h1332 C.h1334 hV2
  obtain ⟨z, a, -, hz0, hz1, ha, haV, -, -⟩ := S14.exists_basis
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haVV : a ∈ V := hV2.2.1 ha
  have hza : z ≠ a := fun e => haV (e ▸ hz0)
  have ha1 : a ≠ 1 := fun e => haV (e ▸ one_mem _)
  have hle : (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ V ≤ conjSub y V := by
    rintro f ⟨hf, hfV⟩
    rcases S.partition_eight' hV1' h8 hf with h1 | h1 | h1
    · exact h1
    · by_cases hf1 : f = 1
      · rw [hf1]; exact one_mem _
      exfalso
      obtain ⟨l, -, hl⟩ : ∃ l ∈ L, l * z * l⁻¹ = f := by
        by_cases hfz : f = z
        · exact ⟨1, one_mem _, by rw [hfz]; group⟩
        · obtain ⟨l, hl, hlz, -⟩ := exists_conj_eq_pair (h.hyp1281One h13322 C.hMod) hzV haVV
            hfV hzV hz1 ha1 hf1 hz1 hza hfz
          exact ⟨l, hl, hlz⟩
      have hmem : (y⁻¹ * l) * z * (y⁻¹ * l)⁻¹ ∈ u0 T V := by
        rw [mem_conjSub] at h1
        rwa [show (y⁻¹ * l) * z * (y⁻¹ * l)⁻¹ = y⁻¹ * (l * z * l⁻¹) * y by group, hl]
      have h2 := (h68 G T L V h).1 z hz0 (y⁻¹ * l) hmem
      have hfZ : f ∈ conjSub x (fsuV1 T V) := by
        rw [← S.hV1, mem_conjSub]
        have e3 : y⁻¹ * f * y = z := by
          rw [← hl]
          calc y⁻¹ * (l * z * l⁻¹) * y = (y⁻¹ * l) * z * (y⁻¹ * l)⁻¹ := by group
            _ = z := h2
        rw [e3]
        exact hz0
      apply hV1'
      have hZU : conjSub x (fsuV1 T V) ≤ fsuU T V := by
        refine le_of_card_eq_two_of_inf_ne_bot C.card_Z fun hb => hf1 ?_
        have : f ∈ conjSub x (fsuV1 T V) ⊓ fsuU T V := ⟨hfZ, hf.1⟩
        rw [hb, Subgroup.mem_bot] at this
        exact this
      have h3 := conjSub_mono y⁻¹ hZU
      rw [← S.hV1, conjSub_conjSub_inv, S.conj_inv_U] at h3
      exact h3
    · exact absurd hfV (C.isF1_not_mem_V h8 h1)
  obtain ⟨-, hV8, -, -, -⟩ := C.hMod G T L V h.hyp h.fsu
  have hF4 : Nat.card ↥((fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ V) = 4 := by
    have := S.card_inf_F hV1 inf_le_left le_sup_left
    rw [hV8] at this
    omega
  have hVy := conjSub_V_eq h C.h1222 C.h1332 C.h1334 C.h63 C.hF inf_le_right hF4 hle
  apply hV1
  have h4 : conjSub y V ≤ conjSub y (fsuU T V) := conjSub_mono y (le_conjClosure V _)
  rw [hVy, S.hU] at h4
  exact inf_le_left.trans h4

theorem false_of_card_u0_four (h68 : Lemma14_7_68) (h674 : Lemma14_7_67_four)
    (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V))
    (hV1' : ¬ fsuV1 T V ≤ conjSub x' (fsuU T V)) (h4 : Nat.card ↥(u0 T V) = 4) : False := by
  have C := S.c
  have h := C.hyp
  have hF := C.hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV1U0 := fsuV1_le_u0 h C.hMod
  have hle : (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ u0 T V ≤ conjSub y (u0 T V) := by
    rintro f ⟨hf, hfU⟩
    exact (S.partition_four' hV1' h4 hf).resolve_right fun h1 => C.isF1_not_mem_u0 h1 hfU
  have hc := S.card_inf_F hV1 hV1U0 le_sup_right
  rw [h4] at hc
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ u0 T V, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hb : (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ u0 T V = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hb, Subgroup.card_bot] at hc
    omega
  have huU0 : u ∈ u0 T V := hu.2
  have huV1 : u ∉ fsuV1 T V := by
    intro h'
    have : u ∈ (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ fsuV1 T V := ⟨hu.1, h'⟩
    rw [C.inf_V1_eq_bot' hV1, Subgroup.mem_bot] at this
    exact hu1 this
  have hidx : (fsuV1 T V).relIndex (u0 T V) = 2 := by
    have := Subgroup.relIndex_mul_card (fsuV1 T V) (u0 T V)
    rw [inf_eq_left.mpr hV1U0, hF.card_V₁, h4] at this
    omega
  have hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    intro t ht
    have htH : t ∈ hz T V := hF.T_le_H ht
    have htu : t * u * t⁻¹ ∈ u0 T V :=
      (Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_u0 h C.hMod htH) u).mp huU0
    have htu1 : t * u * t⁻¹ ∉ fsuV1 T V := fun h' => huV1 (by
      have := (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ htH) u).mpr h'
      exact this)
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t * u * t⁻¹, htu⟩)
      (b := (⟨u, huU0⟩ : ↥(u0 T V))⁻¹)).mpr
    have h2 := key ⟨fun h' => absurd h' htu1, fun h' => absurd (by
      have := inv_mem (Subgroup.mem_subgroupOf.mp h')
      simpa using this) huV1⟩
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have h2 := ((h68 G T L V h).2 u huU0 hu1 hT).2 y (hle hu)
  have hNH : Subgroup.normalizer (u0 T V : Set G) = hz T V := by
    obtain ⟨-, hmax⟩ := (h674 G T L V h).2
    refine hmax _ ⟨u0 T V, ?_, ?_, rfl⟩ (hz_le_normalizer_u0 h C.hMod)
    · intro hb
      have : u ∈ u0 T V := huU0
      rw [hb, Subgroup.mem_bot] at this
      exact hu1 this
    · exact (pCoreOf_isPGroup 2 (hz T V)).to_le ((centralizerMod_le_left _ _ _).trans
        (by rw [fsuU_eq_conjClosure_hz C.hMod h]; exact hF.conjClosure_Vp_le_pCoreOf))
  have hyH : y ∈ hz T V := by
    rw [← hNH]
    exact conjSub_eq_self_iff.mp h2
  apply hV1
  have h3 : conjSub y (fsuV1 T V) = fsuV1 T V := conjSub_eq_self_iff.mpr (hF.H_normalizes_V₁ hyH)
  rw [S.hV1] at h3
  rw [← h3]
  exact Conf69.Z_le

end Sym69

end CFSG.Quasithin.H13.L32A
