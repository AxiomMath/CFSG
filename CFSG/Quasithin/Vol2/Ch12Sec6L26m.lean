module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2
public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26
public import CFSG.Quasithin.Vol2.Ch12Sec6L26k

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom CFSG.SectionRank
open CFSG.Blueprint CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F Equiv
open scoped commutatorElement

namespace S126L26

variable {G : Type} [Group G] [Finite G]

section Bar

variable {T V L V₁ Vp H : Subgroup G}

@[expose] noncomputable def rhoBar (h : HypF91 T V L V₁ Vp H) :
    ↥H ⧸ CFSG.pCore 2 ↥H →* MulAut ↥(tildeOf V₁ (conjClosure Vp H)) :=
  QuotientGroup.lift _ (rhoU h) fun q hq => rhoU_Q h q ((mem_pCore_two_iff q).mp hq)

theorem rhoBar_mk (h : HypF91 T V L V₁ Vp H) (y : ↥H) :
    rhoBar h (y : ↥H ⧸ CFSG.pCore 2 ↥H) = rhoU h y :=
  QuotientGroup.lift_mk _ _ _

theorem rhoBar_ker (h : HypF91 T V L V₁ Vp H) : (rhoBar h).ker = ⊥ := by
  rw [eq_bot_iff]
  intro yb hyb
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  rw [MonoidHom.mem_ker, rhoBar_mk] at hyb
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hyQ : (y : G) ∉ pCoreOf 2 H := fun hq => hy1 ((mk_eq_one_iff y).mpr hq)
  obtain ⟨w, hw⟩ := exists_moved h y.2 hyQ
  have h1 : rhoU h y w = w := by rw [hyb]; rfl
  exact hw h1

theorem comm_mem_tilde (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) {v : G} (hv : v ∈ V) (hvH : v ∈ H)
    (w : ↥(tildeOf V₁ (conjClosure Vp H))) :
    ((w⁻¹ * rhoBar h ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) w :
      ↥(tildeOf V₁ (conjClosure Vp H))) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈
      tildeOf V₁ Vp := by
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  obtain ⟨u, hu, hue⟩ := (mem_tildeOf_iff h.H_normalizes_V₁ hUH).mp w.2
  rw [mem_tildeOf_iff h.H_normalizes_V₁ (h.Vp_le_V.trans h.V_le_H)]
  refine ⟨u⁻¹ * ⟨v, hvH⟩ * u * (⟨v, hvH⟩ : ↥H)⁻¹, ?_, ?_⟩
  · have hc : ⁅(u : G)⁻¹, v⁆ ∈ ⁅conjClosure Vp H, V⁆ :=
      Subgroup.commutator_mem_commutator ((conjClosure Vp H).inv_mem hu) hv
    have e : ⁅(u : G)⁻¹, v⁆ = (u : G)⁻¹ * v * u * v⁻¹ := by
      rw [commutatorElement_def, inv_inv]
    rw [e] at hc
    exact (h.F95_2_aux hidx hV).2.1 hc
  · have e1 : ((w⁻¹ * rhoBar h ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) w :
        ↥(tildeOf V₁ (conjClosure Vp H))) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
        (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)⁻¹ *
          (toTilde h.H_normalizes_V₁ ⟨v, hvH⟩ * w * (toTilde h.H_normalizes_V₁ ⟨v, hvH⟩)⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, rhoBar_mk, rhoU_apply]
    rw [e1, ← hue]
    simp only [map_mul, map_inv]
    group

theorem card_comm_le (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) (hcard : Nat.card Vp = 32) {v : G} (hv : v ∈ V) (hvH : v ∈ H) :
    Nat.card ↥{x : ↥(tildeOf V₁ (conjClosure Vp H)) | ∃ w, x = w⁻¹ *
      rhoBar h ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) w} ≤ 2 ^ 4 := by
  have hle : tildeOf V₁ Vp ≤ tildeOf V₁ (conjClosure Vp H) := secImg_mono (le_conjClosure Vp H)
  have hsub : {x : ↥(tildeOf V₁ (conjClosure Vp H)) | ∃ w, x = w⁻¹ *
      rhoBar h ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) w} ⊆
      {x : ↥(tildeOf V₁ (conjClosure Vp H)) |
        (x : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ Vp} := by
    rintro x ⟨w, rfl⟩
    exact comm_mem_tilde h hidx hV hv hvH w
  calc _ ≤ Nat.card ↥{x : ↥(tildeOf V₁ (conjClosure Vp H)) |
        (x : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ Vp} :=
        Nat.card_mono (Set.toFinite _) hsub
    _ = Nat.card ↥(tildeOf V₁ Vp) :=
        Nat.card_congr
          { toFun := fun x => ⟨x.1.1, x.2⟩
            invFun := fun y => ⟨⟨y.1, hle y.2⟩, y.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    _ = 2 ^ 4 := by
        have := card_tildeOf_mul h.card_V₁ h.V₁_le_Vp
          ((h.Vp_le_V.trans h.V_le_H).trans h.H_normalizes_V₁)
        rw [hcard] at this
        omega

omit [Finite G] in
theorem conj_mem_V₁ (h : HypF91 T V L V₁ Vp H) {y z : G} (hy : y ∈ H) (hz : z ∈ V₁) :
    y⁻¹ * z * y ∈ V₁ := by
  have := (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ (H.inv_mem hy)) z).mp hz
  rwa [inv_inv] at this

theorem exists_comm_mem (h : HypF91 T V L V₁ Vp H) (hidx : Vp.relIndex V = 2)
    (hV : ¬ V ≤ pCoreOf 2 H) {v : G} (hv : v ∈ V) (hvp : v ∉ Vp) :
    ∀ x ∈ Vp, ∃ u ∈ conjClosure Vp H, x⁻¹ * (u⁻¹ * v * u * v⁻¹) ∈ V₁ := by
  have hVpQ : Vp ≤ pCoreOf 2 H := h.Vp_le_pCoreOf_and_commutator_le.1
  have hVpH : Vp ≤ H := h.Vp_le_V.trans h.V_le_H
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hvH : v ∈ H := h.V_le_H hv
  have hsq : ∀ x ∈ Vp, x⁻¹ = x := fun x hx => by
    rw [inv_eq_iff_mul_eq_one, ← sq]
    exact isElemAbelian_pow_eq_one h.elemAbelian_Vp hx
  let S : Subgroup G :=
    { carrier := {x | x ∈ Vp ∧ ∃ u ∈ conjClosure Vp H, x⁻¹ * (u⁻¹ * v * u * v⁻¹) ∈ V₁}
      one_mem' := ⟨Vp.one_mem, 1, (conjClosure Vp H).one_mem, by simp⟩
      mul_mem' := by
        rintro x₁ x₂ ⟨hx₁, u₁, hu₁, h₁⟩ ⟨hx₂, u₂, hu₂, h₂⟩
        refine ⟨Vp.mul_mem hx₁ hx₂, u₁ * u₂, (conjClosure Vp H).mul_mem hu₁ hu₂, ?_⟩
        have hc₁ : u₁⁻¹ * v * u₁ * v⁻¹ ∈ Vp := by
          have := Vp.mul_mem hx₁ (h.V₁_le_Vp h₁)
          rwa [mul_inv_cancel_left] at this
        have he := h.commutator_conjClosure_le _ ((conjClosure Vp H).inv_mem hu₂) _ (hVpQ hc₁)
        have e1 : (x₁ * x₂)⁻¹ * ((u₁ * u₂)⁻¹ * v * (u₁ * u₂) * v⁻¹) =
            ((x₁ * x₂)⁻¹ * (u₂⁻¹ * (u₁⁻¹ * v * u₁ * v⁻¹) * u₂⁻¹⁻¹ *
              (u₁⁻¹ * v * u₁ * v⁻¹)⁻¹) * (x₁ * x₂)) *
              (x₂⁻¹ * (x₁⁻¹ * (u₁⁻¹ * v * u₁ * v⁻¹)) * x₂) *
              (x₂⁻¹ * (u₂⁻¹ * v * u₂ * v⁻¹)) := by group
        rw [e1]
        exact V₁.mul_mem (V₁.mul_mem (conj_mem_V₁ h (H.mul_mem (hVpH hx₁) (hVpH hx₂)) he)
          (conj_mem_V₁ h (hVpH hx₂) h₁)) h₂
      inv_mem' := by
        rintro x ⟨hx, u, hu, hxu⟩
        refine ⟨Vp.inv_mem hx, u, hu, ?_⟩
        rw [inv_inv]
        rw [hsq x hx] at hxu
        exact hxu }
  have hS : ∀ x, x ∈ S ↔ x ∈ Vp ∧ ∃ u ∈ conjClosure Vp H, x⁻¹ * (u⁻¹ * v * u * v⁻¹) ∈ V₁ :=
    fun x => Iff.rfl
  have hV₁S : V₁ ≤ S := fun z hz => (hS z).mpr ⟨h.V₁_le_Vp hz, 1, (conjClosure Vp H).one_mem,
    by simpa using V₁.inv_mem hz⟩
  have hCS : ⁅conjClosure Vp H, V⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro u hu w hw
    have hcp : ⁅u, w⁆ ∈ Vp :=
      (h.F95_2_aux hidx hV).2.1 (Subgroup.commutator_mem_commutator hu hw)
    refine (hS _).mpr ⟨hcp, ?_⟩
    rcases mem_or_inv_mul_mem hidx hv hvp hw with hw5 | hw5
    · refine ⟨1, (conjClosure Vp H).one_mem, ?_⟩
      have h1 := h.commutator_conjClosure_le u hu w (hVpQ hw5)
      have e : ⁅u, w⁆⁻¹ * ((1 : G)⁻¹ * v * 1 * v⁻¹) = (u * w * u⁻¹ * w⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact V₁.inv_mem h1
    · refine ⟨u⁻¹, (conjClosure Vp H).inv_mem hu, ?_⟩
      have h1 := h.commutator_conjClosure_le u hu _ (hVpQ hw5)
      have e : ⁅u, w⁆⁻¹ * (u⁻¹⁻¹ * v * u⁻¹ * v⁻¹) =
          v⁻¹⁻¹ * (u * (v⁻¹ * w) * u⁻¹ * (v⁻¹ * w)⁻¹)⁻¹ * v⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact conj_mem_V₁ h (H.inv_mem hvH) (V₁.inv_mem h1)
  have hVpS : Vp ≤ S := by
    rw [← (h.F95_2_aux hidx hV).1]
    exact sup_le hCS hV₁S
  intro x hx
  exact ((hS x).mp (hVpS hx)).2

end Bar

section Frame

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem not_mem_V1_of_nonsing (F : Frame126 T L V) {y : G} (hy : F.Nonsing y) : y ∉ F.V1 := by
  rintro ⟨z, hz, rfl⟩
  obtain ⟨hzV, hzN⟩ := hy
  have hzW : F.β z ∈ W1 := hz
  have e : (⟨V.subtype z, hzV⟩ : ↥V) = z := rfl
  rw [e] at hzN
  rcases S126L19a.mem_W1 hzW with h1 | h1
  · exact S126T2.ne_one_of_nonsing hzN h1
  · rw [h1] at hzN
    exact S126L1a.not_nonsing_and_wt4 hzN S126L19.hasWt_e0123

omit [Finite G] in
theorem exists_nonsing_coset (F : Frame126 T L V) :
    ∃ x ∈ F.V5, ∀ y : G, x⁻¹ * y ∈ F.V1 → F.Nonsing y := by
  obtain ⟨x₀, hx₀⟩ := F.β_surj (QuotientGroup.mk (pe 0 1) : D8)
  refine ⟨x₀, ⟨x₀, ?_, rfl⟩, fun y hy => ?_⟩
  · show F.β x₀ ∈ W5
    rw [hx₀, S126L24.mem_W5_iff, S126L24.vx_pe]
    decide
  · obtain ⟨z₀, hz₀, hz₀e⟩ := hy
    have hy' : y = (x₀ : G) * z₀ := by
      rw [show (V.subtype z₀ : G) = (z₀ : G) from rfl] at hz₀e
      rw [hz₀e]
      group
    have hyV : y ∈ V := by
      rw [hy']
      exact V.mul_mem x₀.2 z₀.2
    refine ⟨hyV, ?_⟩
    have e : (⟨y, hyV⟩ : ↥V) = x₀ * z₀ := Subtype.ext hy'
    have hzW : F.β z₀ ∈ W1 := hz₀
    rw [e, map_mul, hx₀]
    rcases S126L19a.mem_W1 hzW with h1 | h1
    · rw [h1, mul_one]
      exact S126T2.nonsing_e01
    · rw [h1, S126L19.e0123, ← QuotientGroup.mk_mul]
      exact ⟨_, rfl, by decide⟩

theorem false_of_stab (h1224 : Lemma12_6_24) (h1226' : Stmt12_2_6)
    (h1262 : Theorem12_6_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H)
    (K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))
    (hsol : Group.IsSolvable ↥(K ⊓ Subgroup.centralizer
      ({((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)} : Set (↥H ⧸ CFSG.pCore 2 ↥H))))
    (hns : ∀ w : ↥(tildeOf F.V1 (conjClosure F.V5 H)),
      (∃ u, w = u⁻¹ * rhoBar (setup126 h1224 F hH hZ hHz).1
        ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) u) → w ≠ 1 →
      ¬ Group.IsSolvable ↥(K ⊓ (MulAction.stabilizer
        (MulAut ↥(tildeOf F.V1 (conjClosure F.V5 H))) w).comap
          (rhoBar (setup126 h1224 F hH hZ hHz).1))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (setup126 h1224 F hH hZ hHz).1
  obtain ⟨-, hidx, -, -, -⟩ := setup126 h1224 F hH hZ hHz
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hvQ (hle hv)
  have hvp : v ∉ F.V5 := fun h5 => hvQ (h.Vp_le_pCoreOf_and_commutator_le.1 h5)
  have hUH : conjClosure F.V5 H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hV1H : F.V1 ≤ H := h.V₁_le_V.trans h.V_le_H
  obtain ⟨x, hx5, hxN⟩ := exists_nonsing_coset F
  obtain ⟨u, hu, hxu⟩ := exists_comm_mem h hidx hV hv hvp x hx5
  have hv₂N : F.Nonsing (u⁻¹ * v * u * v⁻¹) := hxN _ hxu
  have huH : u ∈ H := hUH hu
  have hv₂H : u⁻¹ * v * u * v⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem huH) hvH) huH) (H.inv_mem hvH)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥(tildeOf F.V1 (conjClosure F.V5 H)),
      (w₀ : SecQuot (Subgroup.normalizer (F.V1 : Set G)) F.V1) =
        toTilde h.H_normalizes_V₁ ⟨u, huH⟩ :=
    ⟨⟨_, (mem_tildeOf_iff h.H_normalizes_V₁ hUH).mpr ⟨⟨u, huH⟩, hu, rfl⟩⟩, rfl⟩
  set x₀ := w₀⁻¹ * rhoBar h ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) w₀ with hx₀
  have hx₀e : (x₀ : SecQuot (Subgroup.normalizer (F.V1 : Set G)) F.V1) =
      toTilde h.H_normalizes_V₁ ⟨u⁻¹ * v * u * v⁻¹, hv₂H⟩ := by
    have e : (⟨u⁻¹ * v * u * v⁻¹, hv₂H⟩ : ↥H) =
        (⟨u, huH⟩ : ↥H)⁻¹ * ⟨v, hvH⟩ * ⟨u, huH⟩ * (⟨v, hvH⟩ : ↥H)⁻¹ := rfl
    rw [hx₀, Subgroup.coe_mul, Subgroup.coe_inv, rhoBar_mk, rhoU_apply, hw₀, e]
    simp only [map_mul, map_inv]
    group
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun z : ↥(tildeOf F.V1 (conjClosure F.V5 H)) =>
      (z : SecQuot (Subgroup.normalizer (F.V1 : Set G)) F.V1)) h1
    simp only [hx₀e, OneMemClass.coe_one] at h2
    exact not_mem_V1_of_nonsing F hv₂N ((toTilde_eq_one_iff h.H_normalizes_V₁).mp h2)
  apply hns x₀ ⟨w₀, rfl⟩ hx₀1
  set Sb := K ⊓ (MulAction.stabilizer (MulAut ↥(tildeOf F.V1 (conjClosure F.V5 H))) x₀).comap
    (rhoBar h) with hSb
  set Y : Subgroup ↥H := Sb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hY
  have hYc : ∀ y : ↥H, y ∈ Y →
      (y : G) * (u⁻¹ * v * u * v⁻¹) * (y : G)⁻¹ * (u⁻¹ * v * u * v⁻¹)⁻¹ ∈ F.V1 := by
    intro y hy
    have h1 : rhoBar h (y : ↥H ⧸ CFSG.pCore 2 ↥H) x₀ = x₀ := hy.2
    have h2 := congrArg (fun z : ↥(tildeOf F.V1 (conjClosure F.V5 H)) =>
      (z : SecQuot (Subgroup.normalizer (F.V1 : Set G)) F.V1)) h1
    simp only [rhoBar_mk, rhoU_apply, hx₀e] at h2
    have h3 : toTilde h.H_normalizes_V₁ y * toTilde h.H_normalizes_V₁ ⟨_, hv₂H⟩ =
        toTilde h.H_normalizes_V₁ ⟨_, hv₂H⟩ * toTilde h.H_normalizes_V₁ y := by
      calc _ = toTilde h.H_normalizes_V₁ y * toTilde h.H_normalizes_V₁ ⟨_, hv₂H⟩ *
            (toTilde h.H_normalizes_V₁ y)⁻¹ * toTilde h.H_normalizes_V₁ y := by group
        _ = _ := by rw [h2]
    exact (toTilde_comm_iff h.H_normalizes_V₁).mp h3
  have hcen : ∀ z ∈ F.V1, ∀ a : ↥H, z * a = a * z := fun z hz a =>
    Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer a.2) z hz
  let φ : ↥Y →* ↥F.V1 :=
    { toFun := fun y => ⟨((y : ↥H) : G) * (u⁻¹ * v * u * v⁻¹) * ((y : ↥H) : G)⁻¹ *
        (u⁻¹ * v * u * v⁻¹)⁻¹, hYc y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := hYc b b.2
        have ha := hYc a a.2
        set c := u⁻¹ * v * u * v⁻¹ with hc
        show ((a : ↥H) : G) * (b : ↥H) * c * (((a : ↥H) : G) * (b : ↥H))⁻¹ * c⁻¹ =
          (((a : ↥H) : G) * c * ((a : ↥H) : G)⁻¹ * c⁻¹) *
            (((b : ↥H) : G) * c * ((b : ↥H) : G)⁻¹ * c⁻¹)
        have e1 : ((a : ↥H) : G) * (b : ↥H) * c * (((a : ↥H) : G) * (b : ↥H))⁻¹ * c⁻¹ =
            ((a : ↥H) : G) * (((b : ↥H) : G) * c * ((b : ↥H) : G)⁻¹ * c⁻¹) *
              ((a : ↥H) : G)⁻¹ * (((a : ↥H) : G) * c * ((a : ↥H) : G)⁻¹ * c⁻¹) := by group
        rw [e1, ← hcen _ hb (a : ↥H), mul_inv_cancel_right]
        exact (hcen _ hb ⟨_, hV1H ha⟩) }
  have hker : ∀ y : ↥Y, φ y = 1 →
      ((y : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ K ⊓ Subgroup.centralizer
        ({((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)} : Set _) := by
    intro y hy
    refine ⟨y.2.1, ?_⟩
    have h1 : ((y : ↥H) : G) * (u⁻¹ * v * u * v⁻¹) * ((y : ↥H) : G)⁻¹ *
        (u⁻¹ * v * u * v⁻¹)⁻¹ = 1 := congrArg Subtype.val hy
    have hyC : ((y : ↥H) : G) ∈ Subgroup.centralizer ({u⁻¹ * v * u * v⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 := mul_eq_one_iff_eq_inv.mp h1
      rw [inv_inv] at h2
      calc ((y : ↥H) : G) * (u⁻¹ * v * u * v⁻¹) =
          (((y : ↥H) : G) * (u⁻¹ * v * u * v⁻¹) * ((y : ↥H) : G)⁻¹) * ((y : ↥H) : G) := by
            group
        _ = (u⁻¹ * v * u * v⁻¹) * ((y : ↥H) : G) := by rw [h2]
    have hyL := h1262 G T L V F hH _ hv₂N hyC
    have hyNV : ((y : ↥H) : G) ∈ H ⊓ Subgroup.normalizer (V : Set G) := by
      rw [← (h1226' G T L V hH.hyp).2 F.V1 H h.V₁_ne_bot h.V₁_le_V h.H_normalizes_V₁]
      exact ⟨(y : ↥H).2, hyL⟩
    have hyCV : ((y : ↥H) : G) ∈ centralizerMod (pCoreOf 2 H) H V := by
      rw [(h.F95_3 hidx hV).1, (h.F95_3 hidx hV).2]
      exact hyNV
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((mk_comm_iff (y : ↥H) ⟨v, hvH⟩).mpr (hyCV.2.2 v hv))
  have hsolK : Group.IsSolvable ↥φ.ker := by
    let g : ↥φ.ker →* ↥(K ⊓ Subgroup.centralizer
        ({((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)} : Set _)) :=
      { toFun := fun y => ⟨(((y : ↥Y) : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H), hker (y : ↥Y) y.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hg2 : IsPGroup 2 ↥g.ker := by
      intro y
      have hyQ : ((y : ↥φ.ker) : ↥Y).1 ∈ CFSG.pCore 2 ↥H := by
        have h1 := congrArg Subtype.val y.2
        exact (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥H)) ⟨_, hyQ⟩
      refine ⟨n, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hn
    have := hg2.isNilpotent
    exact Group.isSolvable_of_ker_le_range g.ker.subtype g (fun y hy => ⟨⟨y, hy⟩, rfl⟩)
  have hsolY : Group.IsSolvable ↥Y := by
    have : IsMulCommutative ↥F.V1 := ⟨⟨fun a b => Subtype.ext
      (hcen _ b.2 ⟨_, hV1H a.2⟩).symm⟩⟩
    let _ : CommGroup ↥F.V1 := { mul_comm := fun a b => this.is_comm.comm a b }
    exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (fun y hy => ⟨⟨y, hy⟩, rfl⟩)
  let f : ↥Y →* ↥Sb :=
    { toFun := fun y => ⟨((y : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H), y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_surjective (f := f) fun s => ?_
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (s : ↥H ⧸ CFSG.pCore 2 ↥H)
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  show QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈ Sb
  rw [QuotientGroup.mk'_apply, hy]
  exact s.2

theorem false_of_m22 (h1224 : Lemma12_6_24) (h1226' : Stmt12_2_6)
    (h1262 : Theorem12_6_2) (hE : FactM22Twelve12626) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hK : IsHat ↥K (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    (hvN : ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Subgroup.normalizer (K : Set _))
    (hnc : ∃ k ∈ K, ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * k ≠
      k * ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)) : False := by
  have h := (setup126 h1224 F hH hZ hHz).1
  obtain ⟨-, hidx, -, hcard, -⟩ := setup126 h1224 F hH hZ hHz
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hvQ (hle hv)
  have hWe := h.isElemAbelian_tilde
  have hWc : ∀ a b : ↥(tildeOf F.V1 (conjClosure F.V5 H)), a * b = b * a := fun a b =>
    hWe.1.is_comm.comm a b
  have hW2 : ∀ w : ↥(tildeOf F.V1 (conjClosure F.V5 H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hWe.2 w.1 w.2)
  have hv2 : ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 2 = 1 := by
    have hv2' : v ^ 2 = 1 := isElemAbelian_pow_eq_one h.elemAbelian hv
    rw [← QuotientGroup.mk_pow,
      show (⟨v, hvH⟩ : ↥H) ^ 2 = 1 from Subtype.ext (by simpa using hv2'), QuotientGroup.mk_one]
  obtain ⟨hsol, hns⟩ := hE _ _ hWc hW2 (rhoBar h) K hK (by rw [rhoBar_ker, inf_bot_eq]) _ hv2
    hvN hnc (card_comm_le h hidx hV hcard hv hvH)
  exact false_of_stab h1224 h1226' h1262 F hH hZ hHz hv hvH hvQ K hsol hns

end Frame

end S126L26

end CFSG.Quasithin.H13
