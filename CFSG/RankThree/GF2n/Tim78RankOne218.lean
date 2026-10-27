module

public import CFSG.RankThree.GF2n.Tim78Config
public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.Timmesfeld.RankOne.Lift
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_classIn {V W : Subgroup G} {z : G} (hz : z ∈ Subgroup.normalizer (W : Set G))
    {U : Subgroup G} (hU : U ∈ classIn V W) : conjSubgroup z U ∈ classIn V W := by
  obtain ⟨⟨x, rfl⟩, hUW⟩ := hU
  refine ⟨⟨z * x, (conjSubgroup_mul z x V).symm⟩, fun a ha => ?_⟩
  have h1 := hUW (mem_conjSubgroup.mp ha)
  have h2 := (Subgroup.mem_normalizer_iff.mp hz _).mp h1
  rwa [show z * (z⁻¹ * a * z) * z⁻¹ = a by group] at h2

theorem map_conj_map_mk {H R : Subgroup G} [(R.subgroupOf H).Normal] (K : Subgroup G) (z : H) :
    ((K.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H))).map
        (MulAut.conj (QuotientGroup.mk' (R.subgroupOf H) z)).toMonoidHom =
      ((conjSubgroup (z : G) K).subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H)) := by
  rw [Subgroup.map_map]
  have e : (MulAut.conj (QuotientGroup.mk' (R.subgroupOf H) z)).toMonoidHom.comp
      (QuotientGroup.mk' (R.subgroupOf H)) =
      (QuotientGroup.mk' (R.subgroupOf H)).comp (MulAut.conj z).toMonoidHom := by
    ext k
    simp [MulAut.conj_apply]
  rw [e, ← Subgroup.map_map]
  congr 1
  ext k
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨k', hk', rfl⟩
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using hk'
  · intro hk
    refine ⟨z⁻¹ * k * z, ?_, ?_⟩
    · have := mem_conjSubgroup.mp hk
      simpa [mul_assoc] using this
    · group

variable [Finite G]

namespace Hyp218

variable {M V Q P W : Subgroup G} {g : G} (h : Hyp218 M V Q P W g)
include h

omit [Finite G] in
theorem conjSubgroup_P_eq {z z' : G} (hzz : conjSubgroup z V = conjSubgroup z' V) :
    conjSubgroup z P = conjSubgroup z' P := by
  have hm : z'⁻¹ * z ∈ M := by
    rw [← h.normalizer_eq, ← conjSubgroup_eq_self_iff, conjSubgroup_mul, hzz,
      ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have e : conjSubgroup z P = conjSubgroup z' (conjSubgroup (z'⁻¹ * z) P) := by
    rw [← conjSubgroup_mul, mul_inv_cancel_left]
  rw [e, conjSubgroup_eq_self_iff.mpr (h.M_le_normalizer_P hm)]

omit [Finite G] in
theorem conj_P_eq {p u : G} (hpu : conjSubgroup u V = conjSubgroup p (conjSubgroup g V)) :
    conjSubgroup u P = conjSubgroup p (conjSubgroup g P) := by
  rw [← conjSubgroup_mul] at hpu ⊢
  exact h.conjSubgroup_P_eq hpu

theorem sup_eq_W {x : G} (hU : conjSubgroup x V ≤ W) (hUV : conjSubgroup x V ≠ V) :
    V ⊔ conjSubgroup x V = W := by
  have hN : V ≤ Subgroup.normalizer (conjSubgroup x V : Set G) :=
    le_normalizer_of_comm fun v hv u hu => h.W_comm (h.V_le_W hv) (hU hu)
  have hc := PartTwo.Sec6.card_sup_mul_card_inf hN
  rw [h.inf_conj x hUV, Subgroup.card_bot, mul_one, card_conjSubgroup, ← h.card_W] at hc
  exact Subgroup.eq_of_le_of_card_ge (sup_le h.V_le_W hU) (by rw [hc])

theorem mem_centralizer_of_normalizes {p : G} (hp : p ∈ P) {x : G}
    (hU : conjSubgroup x V ≤ W) (hUV : conjSubgroup x V ≠ V)
    (hpU : p ∈ Subgroup.normalizer (conjSubgroup x V : Set G)) :
    p ∈ Subgroup.centralizer (W : Set G) := by
  have h1 := h.comm_of_mem_normalizer (hU.trans h.W_le_P) hUV hp hpU
  refine mem_centralizer_of_forall fun w hw => ?_
  rw [← h.sup_eq_W hU hUV] at hw
  have hN : conjSubgroup x V ≤ Subgroup.normalizer (V : Set G) :=
    le_normalizer_of_comm fun u hu v hv => h.W_comm (hU hu) (h.V_le_W hv)
  obtain ⟨v, hv, u, hu, rfl⟩ := exists_mul_of_mem_sup hN hw
  rw [← mul_assoc, h.central hp hv, mul_assoc, h1 u hu, mul_assoc]

omit [Finite G] in
theorem Pg_comm {u : G} (hu : u ∈ conjSubgroup g P) {a : G} (ha : a ∈ conjSubgroup g V) :
    u * a = a * u := by
  have := h.central (mem_conjSubgroup.mp hu) (mem_conjSubgroup.mp ha)
  calc u * a = g * ((g⁻¹ * u * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * a * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
    _ = a * u := by group

theorem mem_normalizer_Pg {s : G} (hs : ∀ a ∈ conjSubgroup g V, s * a = a * s) :
    s ∈ Subgroup.normalizer (conjSubgroup g P : Set G) := by
  have hm := h.conj_mem_M_of_commute hs
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  rw [SetLike.mem_coe, mem_conjSubgroup] at hu ⊢
  have := conj_mem_of_mem_normalizer (h.M_le_normalizer_P hm) hu
  rwa [show g⁻¹ * s * g * (g⁻¹ * u * g) * (g⁻¹ * s * g)⁻¹ = g⁻¹ * (s * u * s⁻¹) * g by
    group] at this

omit [Finite G] in
theorem comm_V1_of_mem_centralizer {c : G} (hc : c ∈ Subgroup.centralizer (W : Set G))
    {a : G} (ha : a ∈ conjSubgroup g V) : c * a = a * c :=
  (Subgroup.mem_centralizer_iff.mp hc a (h.V1_le_W ha)).symm

section Swap

variable {x : G} (hxW : x ∈ Subgroup.normalizer (W : Set G))
  (hxV : conjSubgroup x V = conjSubgroup g V)
include hxW hxV

theorem Pg_le_normalizer_W : conjSubgroup g P ≤ Subgroup.normalizer (W : Set G) := by
  rw [← h.conjSubgroup_P_eq hxV]
  intro u hu
  have hp : x⁻¹ * u * x ∈ P := mem_conjSubgroup.mp hu
  have e : u = x * (x⁻¹ * u * x) * x⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxW (h.P_le_normalizer_W hp))
    (Subgroup.inv_mem _ hxW)

omit [Finite G] hxW in
theorem conj_inv_ne : conjSubgroup x⁻¹ V ≠ V := by
  intro heq
  apply h.ne
  rw [← hxV, conjSubgroup_eq_self_iff]
  have := Subgroup.inv_mem _ (conjSubgroup_eq_self_iff.mp heq)
  rwa [inv_inv] at this

variable {y : G} (hy : IsOpp V P g y)
include hy

theorem exists_Pg_conj_eq {U U' : Subgroup G} (hU : U ∈ classIn V W)
    (hUV : U ≠ conjSubgroup g V) (hU' : U' ∈ classIn V W) (hU'V : U' ≠ conjSubgroup g V) :
    ∃ u ∈ conjSubgroup g P, conjSubgroup u U = U' := by
  have hx' : x⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hxW
  have hne : ∀ U₀ : Subgroup G, U₀ ≠ conjSubgroup g V → conjSubgroup x⁻¹ U₀ ≠ V := by
    intro U₀ hU₀ heq
    apply hU₀
    rw [← hxV, ← heq, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  obtain ⟨p, hp, hpeq⟩ := h.exists_conj_eq hy (conj_mem_classIn hx' hU) (hne U hUV)
    (conj_mem_classIn hx' hU') (hne U' hU'V)
  refine ⟨x * p * x⁻¹, ?_, ?_⟩
  · rw [← h.conjSubgroup_P_eq hxV, mem_conjSubgroup, show x⁻¹ * (x * p * x⁻¹) * x = p by group]
    exact hp
  · rw [show x * p * x⁻¹ = x * (p * x⁻¹) by group, conjSubgroup_mul, conjSubgroup_mul, hpeq,
      ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]

omit hy in
theorem Pg_conj_ne {u : G} (hu : u ∈ conjSubgroup g P)
    (huW : u ∉ Subgroup.centralizer (W : Set G)) : conjSubgroup u V ≠ V := by
  intro heq
  apply huW
  rw [← h.conjSubgroup_P_eq hxV, mem_conjSubgroup] at hu
  set p := x⁻¹ * u * x with hpdef
  have hU : conjSubgroup x⁻¹ V ≤ W := (conj_mem_classIn (Subgroup.inv_mem _ hxW)
    ⟨⟨1, (conjSubgroup_one V).symm⟩, h.V_le_W⟩).2
  have hpU : p ∈ Subgroup.normalizer (conjSubgroup x⁻¹ V : Set G) := by
    rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_mul, hpdef,
      show x⁻¹ * u * x * x⁻¹ = x⁻¹ * u by group, conjSubgroup_mul, heq]
  have hpW := h.mem_centralizer_of_normalizes hu hU (h.conj_inv_ne hxV) hpU
  have := conj_mem_of_mem_normalizer (mem_normalizer_centralizer hxW) hpW
  rwa [hpdef, show x * (x⁻¹ * u * x) * x⁻¹ = u by group] at this

theorem exists_rankOne_centralizer (hq : 4 ≤ Nat.card V)
    {H : Subgroup G} (hH : H = P ⊔ conjSubgroup g P) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card V = 2 ^ n ∧
      ∃ φ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n), Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf H ∧
        (P.subgroupOf H).map φ = upperUnipotent (GaloisField 2 n) ∧
        ((conjSubgroup g P).subgroupOf H).map φ = lowerUnipotent (GaloisField 2 n) ∧
        IsPGroup 2 (H ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) ∧
        H ⊓ Subgroup.centralizer (W : Set G) =
          (P ⊓ Subgroup.centralizer (W : Set G)) ⊔
            (conjSubgroup g P ⊓ Subgroup.centralizer (W : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Pg := conjSubgroup g P with hPg
  set V₁ := conjSubgroup g V with hV₁
  set C := Subgroup.centralizer (W : Set G) with hCdef
  have hPgW : Pg ≤ Subgroup.normalizer (W : Set G) := h.Pg_le_normalizer_W hxW hxV
  have hPH : P ≤ H := hH ▸ le_sup_left
  have hPgH : Pg ≤ H := hH ▸ le_sup_right
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := hH ▸ sup_le h.P_le_normalizer_W hPgW
  have hCM : C ≤ M := fun c hc => h.mem_M_of_mem_centralizer hc
  have hCW : C ≤ Subgroup.normalizer (W : Set G) := centralizer_le_normalizer_W W
  have hPg2 : IsPGroup 2 Pg := h.isPGroup_P.map _
  set D := P ⊓ C with hD
  set D' := Pg ⊓ C with hD'
  set R₀ := D ⊔ D' with hR₀
  have hD2 : IsPGroup 2 D := h.isPGroup_P.to_le inf_le_left
  have hD'2 : IsPGroup 2 D' := hPg2.to_le inf_le_left
  have hD'ND : D' ≤ Subgroup.normalizer (D : Set G) := fun e he =>
    mem_normalizer_inf (h.M_le_normalizer_P (hCM he.2)) (mem_normalizer_centralizer (hCW he.2))
  have hR₀2 : IsPGroup 2 R₀ := by
    rw [hR₀, sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hD'2 hD2 hD'ND
  have hR₀C : R₀ ≤ C := sup_le inf_le_right inf_le_right
  have hR₀H : R₀ ≤ H := sup_le (inf_le_left.trans hPH) (inf_le_left.trans hPgH)
  have hVR₀ : V ≤ R₀ := le_sup_of_le_left (le_inf h.V_le_P fun v hv =>
    mem_centralizer_of_forall fun w hw => h.W_comm (h.V_le_W hv) hw)
  have hcommC : ∀ z ∈ Subgroup.normalizer (W : Set G), ∀ c ∈ C, ⁅z, c⁆ ∈ C := by
    intro z hz c hc
    rw [commutatorElement_def]
    exact C.mul_mem (conj_mem_of_mem_normalizer (mem_normalizer_centralizer hz) hc)
      (C.inv_mem hc)
  have hcommP : ∀ p ∈ P, ∀ m ∈ M, ⁅p, m⁆ ∈ P := by
    intro p hp m hm
    rw [show ⁅p, m⁆ = p * (m * p⁻¹ * m⁻¹) by rw [commutatorElement_def]; group]
    exact P.mul_mem hp (conj_mem_of_mem_normalizer (h.M_le_normalizer_P hm) (P.inv_mem hp))
  have hcommPg : ∀ u ∈ Pg, ∀ c, (∀ a ∈ V₁, c * a = a * c) → ⁅u, c⁆ ∈ Pg := by
    intro u hu c hc
    rw [show ⁅u, c⁆ = u * (c * u⁻¹ * c⁻¹) by rw [commutatorElement_def]; group]
    exact Pg.mul_mem hu (conj_mem_of_mem_normalizer (h.mem_normalizer_Pg hc) (Pg.inv_mem hu))
  have hcommC1 : ∀ c ∈ C, ∀ a ∈ V₁, c * a = a * c := fun c hc a ha =>
    h.comm_V1_of_mem_centralizer hc ha
  have hPR₀ : P ≤ Subgroup.normalizer (R₀ : Set G) := by
    intro p hp
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hle : R₀ ≤ R₀.comap (MulAut.conj p).toMonoidHom := by
      refine sup_le (fun d hd => ?_) (fun e he => ?_)
      · exact le_sup_left (a := D) (conj_mem_of_mem_normalizer
          (mem_normalizer_inf (h.M_le_normalizer_P (h.P_le_M hp))
            (mem_normalizer_centralizer (h.P_le_normalizer_W hp))) hd)
      · have h1 : ⁅p, e⁆ ∈ D := ⟨hcommP p hp e (hCM he.2), hcommC p
          (h.P_le_normalizer_W hp) e he.2⟩
        show p * e * p⁻¹ ∈ R₀
        rw [show p * e * p⁻¹ = ⁅p, e⁆ * e by rw [commutatorElement_def]; group]
        exact R₀.mul_mem (le_sup_left (a := D) h1) (le_sup_right (b := D') he)
    exact hle hr
  have hPgR₀ : Pg ≤ Subgroup.normalizer (R₀ : Set G) := by
    intro u hu
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hle : R₀ ≤ R₀.comap (MulAut.conj u).toMonoidHom := by
      refine sup_le (fun d hd => ?_) (fun e he => ?_)
      · have h1 : ⁅u, d⁆ ∈ D' := ⟨hcommPg u hu d (hcommC1 d hd.2), hcommC u (hPgW hu) d hd.2⟩
        show u * d * u⁻¹ ∈ R₀
        rw [show u * d * u⁻¹ = ⁅u, d⁆ * d by rw [commutatorElement_def]; group]
        exact R₀.mul_mem (le_sup_right (b := D') h1) (le_sup_left (a := D) hd)
      · exact le_sup_right (b := D') (conj_mem_of_mem_normalizer
          (mem_normalizer_inf (h.mem_normalizer_Pg fun a ha => h.Pg_comm hu ha)
            (mem_normalizer_centralizer (hPgW hu))) he)
    exact hle hr
  have hHR₀ : H ≤ Subgroup.normalizer (R₀ : Set G) := hH ▸ sup_le hPR₀ hPgR₀
  have hcommL : ∀ z ∈ H, ∀ l ∈ H ⊓ C, ⁅z, l⁆ ∈ R₀ := by
    let T : Subgroup G :=
      { carrier := {z | z ∈ H ∧ ∀ l ∈ H ⊓ C, ⁅z, l⁆ ∈ R₀}
        one_mem' := ⟨H.one_mem, fun l _ => by simp⟩
        mul_mem' := by
          rintro z₁ z₂ ⟨hz₁, h₁⟩ ⟨hz₂, h₂⟩
          refine ⟨H.mul_mem hz₁ hz₂, fun l hl => ?_⟩
          rw [show ⁅z₁ * z₂, l⁆ = z₁ * ⁅z₂, l⁆ * z₁⁻¹ * ⁅z₁, l⁆ by
            simp only [commutatorElement_def]; group]
          exact R₀.mul_mem (conj_mem_of_mem_normalizer (hHR₀ hz₁) (h₂ l hl)) (h₁ l hl)
        inv_mem' := by
          rintro z ⟨hz, h₁⟩
          refine ⟨H.inv_mem hz, fun l hl => ?_⟩
          rw [show ⁅z⁻¹, l⁆ = z⁻¹ * ⁅z, l⁆⁻¹ * z⁻¹⁻¹ by
            simp only [commutatorElement_def]; group]
          exact conj_mem_of_mem_normalizer (hHR₀ (H.inv_mem hz)) (R₀.inv_mem (h₁ l hl)) }
    have hPT : P ≤ T := fun p hp => ⟨hPH hp, fun l hl =>
      le_sup_left (a := D) ⟨hcommP p hp l (hCM hl.2), hcommC p (h.P_le_normalizer_W hp) l hl.2⟩⟩
    have hPgT : Pg ≤ T := fun u hu => ⟨hPgH hu, fun l hl =>
      le_sup_right (b := D') ⟨hcommPg u hu l (hcommC1 l hl.2), hcommC u (hPgW hu) l hl.2⟩⟩
    have hHT : H ≤ T := hH ▸ sup_le hPT hPgT
    exact fun z hz => (hHT hz).2
  have hR₀n : (R₀.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR₀H).mpr hHR₀
  set π := QuotientGroup.mk' (R₀.subgroupOf H) with hπdef
  have hπ1 : ∀ z : H, π z = 1 ↔ (z : G) ∈ R₀ := fun z => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ z z' : H, π z = π z' ↔ (z : G)⁻¹ * z' ∈ R₀ := fun z z' => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    rfl
  set A := (P.subgroupOf H).map π with hA
  set B := (Pg.subgroupOf H).map π with hB
  have hmemA : ∀ a ∈ A, ∃ p : H, (p : G) ∈ P ∧ π p = a := fun a ha => by
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨p, Subgroup.mem_subgroupOf.mp hp, rfl⟩
  have hmemB : ∀ b ∈ B, ∃ u : H, (u : G) ∈ Pg ∧ π u = b := fun b hb => by
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hb
    exact ⟨u, Subgroup.mem_subgroupOf.mp hu, rfl⟩
  have hπA : ∀ p : H, (p : G) ∈ P → π p ∈ A := fun p hp =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
  have hπB : ∀ u : H, (u : G) ∈ Pg → π u ∈ B := fun u hu =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
  have hPC : ∀ p : H, (p : G) ∈ P → π p ≠ 1 → (p : G) ∉ C := fun p hp hp1 hpC =>
    hp1 ((hπ1 p).mpr (le_sup_left (a := D) ⟨hp, hpC⟩))
  have hPgC : ∀ u : H, (u : G) ∈ Pg → π u ≠ 1 → (u : G) ∉ C := fun u hu hu1 huC =>
    hu1 ((hπ1 u).mpr (le_sup_right (b := D') ⟨hu, huC⟩))
  have hV1cls : V₁ ∈ classIn V W := ⟨⟨g, rfl⟩, h.V1_le_W⟩
  have hVcls : V ∈ classIn V W := ⟨⟨1, (conjSubgroup_one V).symm⟩, h.V_le_W⟩
  have hrank : IsElemAbRankOne A B := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hA, hB, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hPH hPgH, ← hH,
        Subgroup.subgroupOf_self]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    · intro hAB
      obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (h.conj_ne_bot y)
      have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
      have hbP : b ∈ P := hy.le hb
      have hmem : π ⟨b, hPH hbP⟩ ∈ B := hAB ▸ hπA _ hbP
      obtain ⟨u, hu, hub⟩ := hmemB _ hmem
      have hr : (u : G)⁻¹ * b ∈ C := hR₀C ((hπeq u ⟨b, hPH hbP⟩).mp hub)
      apply hb1'
      refine hy.cent b hb fun a ha => ?_
      have h1 := hcommC1 _ hr a ha
      have h2 := h.Pg_comm hu ha
      calc b * a = (u : G) * (((u : G)⁻¹ * b) * a) := by group
        _ = (u : G) * (a * ((u : G)⁻¹ * b)) := by rw [h1]
        _ = ((u : G) * a) * ((u : G)⁻¹ * b) := by group
        _ = (a * u) * ((u : G)⁻¹ * b) := by rw [h2]
        _ = a * b := by group
    · intro a ha a' ha'
      obtain ⟨p, hp, rfl⟩ := hmemA a ha
      obtain ⟨p', hp', rfl⟩ := hmemA a' ha'
      show π p * π p' = π p' * π p
      rw [← map_mul, ← map_mul, hπeq]
      have : ((p * p' : H) : G)⁻¹ * ((p' * p : H) : G) = ⁅(p' : G)⁻¹, (p : G)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, commutatorElement_def]; group
      rw [this]
      exact hVR₀ (h.commutator_mem (P.inv_mem hp') (P.inv_mem hp))
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := hmemA a ha
      rw [← map_mul, hπ1]
      have : ((p * p : H) : G) = (p : G) ^ 2 := by rw [Subgroup.coe_mul, pow_two]
      rw [this]
      exact hVR₀ (h.sq_mem hp)
    · intro a ha ha1
      obtain ⟨p, hp, rfl⟩ := hmemA a ha
      have hpC := hPC p hp ha1
      have hU : conjSubgroup (p : G) V₁ ∈ classIn V W :=
        conj_mem_classIn (h.P_le_normalizer_W hp) hV1cls
      have hUV1 : conjSubgroup (p : G) V₁ ≠ V₁ := fun heq =>
        hpC (h.mem_centralizer_W hp (conjSubgroup_eq_self_iff.mp heq))
      have hUV : conjSubgroup (p : G) V₁ ≠ V := by
        rw [hV₁, ← conjSubgroup_mul]
        exact h.conj_V1_ne hp
      obtain ⟨u, hu, hueq⟩ := h.exists_Pg_conj_eq hxW hxV hy hVcls h.ne.symm hU hUV1
      refine ⟨π ⟨u, hPgH hu⟩, hπB _ hu, fun hu1 => ?_, ?_⟩
      · have huC : u ∈ C := hR₀C ((hπ1 _).mp hu1)
        apply hUV
        rw [← hueq, conjSubgroup_eq_self_iff]
        refine Subgroup.mem_normalizer_fintype fun v hv => ?_
        rw [(Subgroup.mem_centralizer_iff.mp huC v (h.V_le_W hv)).symm, mul_inv_cancel_right]
        exact hv
      · rw [hA, hB, map_conj_map_mk P, map_conj_map_mk Pg]
        congr 2
        exact h.conj_P_eq hueq
    · intro b hb hb1
      obtain ⟨u, hu, rfl⟩ := hmemB b hb
      have huC := hPgC u hu hb1
      have huV : conjSubgroup (u : G) V ≠ V := h.Pg_conj_ne hxW hxV hu huC
      have hU : conjSubgroup (u : G) V ∈ classIn V W := conj_mem_classIn (hPgW hu) hVcls
      have hUV1 : conjSubgroup (u : G) V ≠ V₁ := by
        intro heq
        apply h.ne
        have hn : (u : G) ∈ Subgroup.normalizer (V₁ : Set G) :=
          Subgroup.mem_normalizer_fintype fun a ha => by
            rw [h.Pg_comm hu ha, mul_inv_cancel_right]
            exact ha
        have e : conjSubgroup (u : G) V = conjSubgroup (u : G) V₁ := by
          rw [heq, conjSubgroup_eq_self_iff.mpr hn]
        exact (Subgroup.map_injective (MulAut.conj (u : G)).injective e).symm
      obtain ⟨p, hp, hpeq⟩ := h.exists_conj_eq hy hV1cls h.ne hU huV
      refine ⟨π ⟨p, hPH hp⟩, hπA _ hp, fun hp1 => ?_, ?_⟩
      · have hpC' : p ∈ C := hR₀C ((hπ1 _).mp hp1)
        apply hUV1
        rw [← hpeq, conjSubgroup_eq_self_iff]
        refine Subgroup.mem_normalizer_fintype fun a ha => ?_
        rw [(Subgroup.mem_centralizer_iff.mp hpC' a (h.V1_le_W ha)).symm, mul_inv_cancel_right]
        exact ha
      · rw [hA, hB, map_conj_map_mk P, map_conj_map_mk Pg]
        congr 2
        exact (h.conj_P_eq hpeq.symm).symm
  have hAcard : Nat.card A = Nat.card V := by
    let f : conjSubgroup y V → A := fun b => ⟨π ⟨b, hPH (hy.le b.2)⟩, hπA _ (hy.le b.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro b b' hbb'
        have h1 : π ⟨b, hPH (hy.le b.2)⟩ = π ⟨b', hPH (hy.le b'.2)⟩ := congrArg Subtype.val hbb'
        have hr := hR₀C ((hπeq _ _).mp h1)
        have hmem : (b : G)⁻¹ * b' ∈ conjSubgroup y V :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ b.2) b'.2
        have := hy.cent _ hmem fun a ha => hcommC1 _ hr a ha
        apply Subtype.ext
        calc (b : G) = b * ((b : G)⁻¹ * b') := by rw [this, mul_one]
          _ = b' := by group
      · rintro ⟨a, ha⟩
        obtain ⟨p, hp, rfl⟩ := hmemA a ha
        obtain ⟨b, hb, hbp⟩ := h.exists_mem_mul_mem_centralizer hy hp
        refine ⟨⟨b, hb⟩, Subtype.ext ((hπeq _ _).mpr ?_)⟩
        exact le_sup_left (a := D) ⟨P.mul_mem (P.inv_mem (hy.le hb)) hp, hbp⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf), card_conjSubgroup]
  obtain ⟨n, hn2, hAn, φ₀, hφA, hφB⟩ := rankOne_mulEquiv_SL2 hrank (hAcard ▸ hq)
  have hLR₀ : H ⊓ C ≤ R₀ := by
    intro l hl
    have hlH : l ∈ H := (Subgroup.mem_inf.mp hl).1
    have hcen : φ₀ (π ⟨l, hlH⟩) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
        (GaloisField 2 n)) := by
      rw [Subgroup.mem_center_iff]
      intro m
      obtain ⟨ξ, rfl⟩ := φ₀.surjective m
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (R₀.subgroupOf H) ξ
      have hc : π z * π ⟨l, hlH⟩ = π ⟨l, hlH⟩ * π z := by
        rw [← map_mul, ← map_mul, hπeq]
        have e : ((z * ⟨l, hlH⟩ : H) : G)⁻¹ * ((⟨l, hlH⟩ * z : H) : G) =
            l⁻¹ * ⁅(z : G)⁻¹, l⁆ * l⁻¹⁻¹ := by
          simp only [Subgroup.coe_mul, commutatorElement_def]; group
        rw [e]
        exact conj_mem_of_mem_normalizer (hHR₀ (H.inv_mem hlH))
          (hcommL _ (H.inv_mem z.2) l hl)
      exact (map_mul φ₀ _ _).symm.trans ((congrArg φ₀ hc).trans (map_mul φ₀ _ _))
    rw [RankOne.center_SL2_eq_bot, Subgroup.mem_bot, map_eq_one_iff _ φ₀.injective] at hcen
    exact (hπ1 _).mp hcen
  have hR₀eq : R₀ = H ⊓ C := le_antisymm (le_inf hR₀H hR₀C) hLR₀
  refine ⟨n, hn2, hAcard ▸ hAn, φ₀.toMonoidHom.comp π,
    φ₀.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_, ?_, hR₀eq ▸ hR₀2, hR₀eq.symm⟩
  · ext z
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ φ₀.injective, hπ1, Subgroup.mem_subgroupOf, hR₀eq]
    exact ⟨fun hz => hz.2, fun hz => ⟨z.2, hz⟩⟩
  · rw [← Subgroup.map_map, ← hA]
    exact hφA
  · rw [← Subgroup.map_map, ← hB]
    exact hφB

theorem exists_rankOne (hq : 4 ≤ Nat.card V) {H : Subgroup G}
    (hH : H = P ⊔ conjSubgroup g P) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card V = 2 ^ n ∧
      ∃ φ : H →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n), Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf H ∧
        (P.subgroupOf H).map φ = upperUnipotent (GaloisField 2 n) ∧
        ((conjSubgroup g P).subgroupOf H).map φ = lowerUnipotent (GaloisField 2 n) ∧
        IsPGroup 2 (H ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) := by
  obtain ⟨n, hn2, hn, φ, hφ, hker, hP, hPg, h2, -⟩ :=
    h.exists_rankOne_centralizer hxW hxV hy hq hH
  exact ⟨n, hn2, hn, φ, hφ, hker, hP, hPg, h2⟩

theorem inf_centralizer_W_eq_sup (hq : 4 ≤ Nat.card V)
    {H : Subgroup G} (hH : H = P ⊔ conjSubgroup g P) :
    H ⊓ Subgroup.centralizer (W : Set G) =
      (P ⊓ Subgroup.centralizer (W : Set G)) ⊔
        (conjSubgroup g P ⊓ Subgroup.centralizer (W : Set G)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, he⟩ := h.exists_rankOne_centralizer hxW hxV hy hq hH
  exact he

end Swap

end Hyp218

end CFSG.RankThree.GF2n.Tim78
