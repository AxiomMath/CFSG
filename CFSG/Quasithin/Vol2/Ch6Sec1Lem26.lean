module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem24
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem6
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem20Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement MatrixGroups

section SumNatural

variable {G : Type} [Group G]

theorem relIndex_eq_of_sumNatural {F : Type*} [Field F] [Finite F] {s : ℕ}
    {X R E : Subgroup G} (hsum : IsSumOfNaturalSL2ModulesOver F s X R R E) :
    E.relIndex R = (Nat.card F ^ 2) ^ s := by
  obtain ⟨-, φ, -, -, hφs, hφk, -⟩ := hsum
  have hker : φ.ker = E.subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφk x
  have hcard : Nat.card (Multiplicative (Fin s → Fin 2 → F)) = (Nat.card F ^ 2) ^ s := by
    rw [Nat.card_congr Multiplicative.toAdd]
    simp only [Nat.card_fun, Nat.card_fin]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs,
    Subgroup.card_top, hcard]

theorem le_of_sumNatural_one {F : Type*} [Field F] {X R E Y : Subgroup G}
    (hsum : IsSumOfNaturalSL2ModulesOver F 1 X R R E) (hEY : E ≤ Y) (hYR : Y ≤ R)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ Y ≤ E) : R ≤ Y := by
  obtain ⟨β, φ, hβs, -, -, hφk, heqv⟩ := hsum
  obtain ⟨y, hyY, hyE⟩ := Set.not_subset.mp hY
  have hw : Multiplicative.toAdd (φ ⟨y, hYR hyY⟩) 0 ≠ 0 := by
    intro h0
    apply hyE
    refine (hφk ⟨y, hYR hyY⟩).mp ?_
    apply Multiplicative.toAdd.injective
    funext j
    rw [Subsingleton.elim j 0, h0]
    rfl
  intro r hr
  by_cases hv : Multiplicative.toAdd (φ ⟨r, hr⟩) 0 = 0
  · refine hEY ((hφk ⟨r, hr⟩).mp ?_)
    apply Multiplicative.toAdd.injective
    funext j
    rw [Subsingleton.elim j 0, hv]
    rfl
  obtain ⟨A, hA⟩ := SL2Model.exists_smul_eq _ _ hw hv
  obtain ⟨m, hm⟩ := hβs A
  have hmy : (m : G) * y * (m : G)⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp (hXY m.2) y).mp hyY
  have hφz : φ ⟨(m : G) * y * (m : G)⁻¹, hYR hmy⟩ = φ ⟨r, hr⟩ := by
    rw [heqv m ⟨y, hYR hyY⟩ ⟨(m : G) * y * (m : G)⁻¹, hYR hmy⟩ rfl]
    apply Multiplicative.toAdd.injective
    funext j
    rw [Subsingleton.elim j 0]
    show β m • Multiplicative.toAdd (φ ⟨y, hYR hyY⟩) 0 = Multiplicative.toAdd (φ ⟨r, hr⟩) 0
    rw [hm, hA]
  have hz : (((⟨(m : G) * y * (m : G)⁻¹, hYR hmy⟩ : ↥R)⁻¹ * ⟨r, hr⟩ : ↥R) : G) ∈ E :=
    (hφk _).mp (by rw [map_mul, map_inv, hφz, inv_mul_cancel])
  have e : r = (m : G) * y * (m : G)⁻¹ *
      (((⟨(m : G) * y * (m : G)⁻¹, hYR hmy⟩ : ↥R)⁻¹ * ⟨r, hr⟩ : ↥R) : G) := by
    show r = (m : G) * y * (m : G)⁻¹ * (((m : G) * y * (m : G)⁻¹)⁻¹ * r)
    group
  rw [e]
  exact Y.mul_mem hmy (hEY hz)

end SumNatural

section Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_centralizer_of_le_sup {E L L₀ R : Subgroup G} (hLle : L ≤ L₀ ⊔ R)
    (hCL : E ⊓ Subgroup.centralizer (L : Set G) = ⊥) {x : G} (hxE : x ∈ E)
    (hx₀ : x ∈ Subgroup.centralizer (L₀ : Set G)) (hxR : x ∈ Subgroup.centralizer (R : Set G)) :
    x = 1 := by
  have h1 : L₀ ⊔ R ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx₀ y hy))
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxR y hy))
  have hxL : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (h1 (hLle hy))
  have hx : x ∈ E ⊓ Subgroup.centralizer (L : Set G) := ⟨hxE, hxL⟩
  rw [hCL] at hx
  exact Subgroup.mem_bot.mp hx

theorem sup_eq_of_relIndex_le_card {V E F : Subgroup G} (hVE : V ≤ E) (hFE : F ≤ E)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hVF : V ⊓ F = ⊥)
    (hidx : F.relIndex E ≤ Nat.card V) : V ⊔ F = E := by
  have hle : V ⊔ F ≤ E := sup_le hVE hFE
  have hVN : V ≤ Subgroup.normalizer (F : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun f hf =>
      hEab f (hFE hf) v (hVE hv))
  have h1 : F.relIndex (V ⊔ F) = Nat.card V := by
    rw [relIndex_sup_eq_relIndex_of_le_normalizer hVN]
    have h2 := Subgroup.relIndex_mul_card F V
    rw [inf_comm, hVF, Subgroup.card_bot, mul_one] at h2
    exact h2
  have h3 := Subgroup.relIndex_mul_relIndex F (V ⊔ F) E le_sup_right hle
  rw [h1] at h3
  have hpos : 0 < Nat.card V := Nat.card_pos
  have h5 : (V ⊔ F).relIndex E ≠ 0 := relIndex_ne_zero' E (V ⊔ F)
  have h4 : (V ⊔ F).relIndex E = 1 := by
    by_contra h6
    have h7 : Nat.card V * 2 ≤ Nat.card V * (V ⊔ F).relIndex E :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h4)

theorem lemma_6_1_26_core {V Z E R A L₀ L : Subgroup G}
    (hVE : V ≤ E) (hEA : E ≤ A) (hAR : A ≤ R) (hAE : ¬ A ≤ E) (hZV : Z ≤ V)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEZ : E ≤ Subgroup.centralizer (Z : Set G))
    (hER : ∀ e ∈ E, ∀ r ∈ R, e⁻¹ * r * e * r⁻¹ ∈ V)
    (hRV : R ≤ Subgroup.centralizer (V : Set G))
    (hRE : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ E)
    (hEAZ : ∀ f ∈ E, ∀ u ∈ A, f * u * f⁻¹ * u⁻¹ ∈ Z)
    (hL₀R : L₀ ≤ Subgroup.normalizer (R : Set G)) (hLle : L ≤ L₀ ⊔ R)
    (hirr : ∀ Y : Subgroup G, E ≤ Y → Y ≤ R → L₀ ⊔ R ≤ Subgroup.normalizer (Y : Set G) →
      ¬ Y ≤ E → R ≤ Y)
    (hVirr : ∀ P : Subgroup G, P ≤ V → L ≤ Subgroup.normalizer (P : Set G) → P = ⊥ ∨ P = V)
    (hCL : E ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hdec : V ⊔ (E ⊓ Subgroup.centralizer (L₀ : Set G)) = E) :
    (∀ e ∈ E, e ∉ V → ∀ v ∈ V, ∃ r ∈ R, r * e * r⁻¹ = e * v) ∧
      V.relIndex E ≤ Nat.card Z := by
  have hkill : ∀ x ∈ E, x ∈ Subgroup.centralizer (L₀ : Set G) →
      x ∈ Subgroup.centralizer (R : Set G) → x = 1 := fun x hxE hx₀ hxR =>
    eq_one_of_mem_centralizer_of_le_sup hLle hCL hxE hx₀ hxR
  have hEV : E ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun v hv => hEab v (hVE hv) x hx
  have hFNV : E ⊓ Subgroup.centralizer (L₀ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    (inf_le_left.trans hEV).trans (Subgroup.centralizer_le_normalizer _)
  have hYP : ∀ P : Subgroup G, P ≤ E ⊓ Subgroup.centralizer (L₀ : Set G) →
      E ≤ R ⊓ Subgroup.centralizer (P : Set G) ∧
      L₀ ⊔ R ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
    intro P hP
    have hEY : E ≤ R ⊓ Subgroup.centralizer (P : Set G) := fun x hx =>
      ⟨hAR (hEA hx), Subgroup.mem_centralizer_iff.mpr fun p hp => hEab p (hP hp).1 x hx⟩
    refine ⟨hEY, sup_le (fun y hy => ?_) (fun y hy => ?_)⟩
    · refine mem_normalizer_of_forall_conj_mem_of_le fun z hz => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hL₀R hy) z).mp hz.1
      · rw [Subgroup.mem_centralizer_iff]
        intro p hp
        have hyp : y * p = p * y := Subgroup.mem_centralizer_iff.mp (hP hp).2 y hy
        have hpz : p * z = z * p := Subgroup.mem_centralizer_iff.mp hz.2 p hp
        have e1 : y * p * y⁻¹ = p := by rw [hyp, mul_inv_cancel_right]
        calc p * (y * z * y⁻¹) = y * p * y⁻¹ * (y * z * y⁻¹) := by rw [e1]
          _ = y * (p * z) * y⁻¹ := by group
          _ = y * (z * p) * y⁻¹ := by rw [hpz]
          _ = y * z * y⁻¹ * (y * p * y⁻¹) := by group
          _ = y * z * y⁻¹ * p := by rw [e1]
    · refine mem_normalizer_of_forall_conj_mem_of_le fun z hz => ?_
      have e : y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
      rw [e]
      exact Subgroup.mul_mem _ (hEY (hRE y hy z hz.1)) hz
  refine ⟨fun e he heV w hw => ?_, ?_⟩
  ·
    have he' : e ∈ ((V ⊔ (E ⊓ Subgroup.centralizer (L₀ : Set G)) : Subgroup G) : Set G) := by
      rw [hdec]
      exact he
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hFNV] at he'
    obtain ⟨v₀, hv₀, f, ⟨hfE, hf₀⟩, rfl⟩ := Set.mem_mul.mp he'
    have hfV : f ∉ V := fun hfV => heV (V.mul_mem hv₀ hfV)
    let ψ : ↥R →* G := MonoidHom.mk' (fun r => f⁻¹ * (r : G) * f * (r : G)⁻¹) (by
      intro r s
      have hc : (f⁻¹ * (s : G) * f * (s : G)⁻¹) * r = r * (f⁻¹ * (s : G) * f * (s : G)⁻¹) :=
        Subgroup.mem_centralizer_iff.mp (hRV r.2) _ (hER f hfE s s.2)
      show f⁻¹ * ((r : G) * s) * f * ((r : G) * s)⁻¹ =
        f⁻¹ * (r : G) * f * (r : G)⁻¹ * (f⁻¹ * (s : G) * f * (s : G)⁻¹)
      calc f⁻¹ * ((r : G) * s) * f * ((r : G) * s)⁻¹ =
          f⁻¹ * r * f * (r : G)⁻¹ * ((r : G) * (f⁻¹ * s * f * (s : G)⁻¹) * (r : G)⁻¹) := by
            group
        _ = f⁻¹ * r * f * (r : G)⁻¹ * (f⁻¹ * s * f * (s : G)⁻¹) := by
            rw [← hc]
            group)
    have hψ : ∀ r : ↥R, ψ r = f⁻¹ * (r : G) * f * (r : G)⁻¹ := fun r => rfl
    have hPV : ψ.range ≤ V := by
      intro p hp
      obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hp
      exact hER f hfE r r.2
    have hPN : L ≤ Subgroup.normalizer (ψ.range : Set G) := by
      refine hLle.trans (sup_le (fun y hy => ?_) (fun y hy => ?_))
      · refine mem_normalizer_of_forall_conj_mem_of_le fun p hp => ?_
        obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hp
        have hyr : y * (r : G) * y⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hL₀R hy) r).mp r.2
        refine MonoidHom.mem_range.mpr ⟨⟨_, hyr⟩, ?_⟩
        have hyf : y * f = f * y := Subgroup.mem_centralizer_iff.mp hf₀ y hy
        have e1 : y⁻¹ * f * y = f := by rw [mul_assoc, ← hyf, inv_mul_cancel_left]
        have e2 : y⁻¹ * f⁻¹ * y = f⁻¹ := by
          calc y⁻¹ * f⁻¹ * y = (y⁻¹ * f * y)⁻¹ := by group
            _ = f⁻¹ := by rw [e1]
        show f⁻¹ * (y * (r : G) * y⁻¹) * f * (y * (r : G) * y⁻¹)⁻¹ =
          y * (f⁻¹ * (r : G) * f * (r : G)⁻¹) * y⁻¹
        calc f⁻¹ * (y * (r : G) * y⁻¹) * f * (y * (r : G) * y⁻¹)⁻¹
            = y * (y⁻¹ * f⁻¹ * y) * r * (y⁻¹ * f * y) * (r : G)⁻¹ * y⁻¹ := by group
          _ = y * (f⁻¹ * (r : G) * f * (r : G)⁻¹) * y⁻¹ := by
            rw [e1, e2]
            group
      · refine mem_normalizer_of_forall_conj_mem_of_le fun p hp => ?_
        have hc : p * y = y * p := Subgroup.mem_centralizer_iff.mp (hRV hy) p (hPV hp)
        rw [← hc, mul_inv_cancel_right]
        exact hp
    rcases hVirr _ hPV hPN with h0 | h0
    ·
      exfalso
      have hfR : f ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have h1 : ψ ⟨r, hr⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
        rw [h0, Subgroup.mem_bot] at h1
        have h1' : f⁻¹ * r * f * r⁻¹ = 1 := h1
        calc r * f = f * (f⁻¹ * r * f * r⁻¹) * r := by group
          _ = f * r := by rw [h1', mul_one]
      exact hfV (by rw [hkill f hfE hf₀ hfR]; exact V.one_mem)
    ·
      have hwP : w ∈ ψ.range := by
        rw [h0]
        exact hw
      obtain ⟨⟨r, hr⟩, hrw⟩ := MonoidHom.mem_range.mp hwP
      refine ⟨r, hr, ?_⟩
      have hrw' : f⁻¹ * r * f * r⁻¹ = w := hrw
      have hc : v₀ * r = r * v₀ := Subgroup.mem_centralizer_iff.mp (hRV hr) v₀ hv₀
      calc r * (v₀ * f) * r⁻¹ = (r * v₀) * f * r⁻¹ := by group
        _ = v₀ * (f * (f⁻¹ * r * f * r⁻¹)) := by
          rw [← hc]
          group
        _ = v₀ * f * w := by
          rw [hrw']
          group
  ·
    by_cases hFR : E ⊓ Subgroup.centralizer (L₀ : Set G) ≤ Subgroup.centralizer (R : Set G)
    ·
      have hF1 : E ⊓ Subgroup.centralizer (L₀ : Set G) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (hkill x hx.1 hx.2 (hFR hx))
      rw [hF1, sup_bot_eq] at hdec
      rw [hdec, Subgroup.relIndex_self]
      exact Nat.card_pos
    ·
      obtain ⟨hE1, hN1⟩ := hYP _ le_rfl
      have hY1 : R ⊓ Subgroup.centralizer
          ((E ⊓ Subgroup.centralizer (L₀ : Set G) : Subgroup G) : Set G) ≤ E := by
        by_contra hcon
        apply hFR
        rw [Subgroup.le_centralizer_iff]
        exact (hirr _ hE1 inf_le_left hN1 hcon).trans inf_le_right
      obtain ⟨u, huA, huE⟩ := Set.not_subset.mp hAE
      have huR : u ∈ R := hAR huA
      have hFu : (E ⊓ Subgroup.centralizer (L₀ : Set G)) ⊓
          Subgroup.centralizer ({u} : Set G) = ⊥ := by
        obtain ⟨hE2, hN2⟩ := hYP _ inf_le_left
        have hu2 : u ∈ R ⊓ Subgroup.centralizer
            (((E ⊓ Subgroup.centralizer (L₀ : Set G)) ⊓ Subgroup.centralizer ({u} : Set G) :
              Subgroup G) : Set G) :=
          ⟨huR, Subgroup.mem_centralizer_iff.mpr fun p hp =>
            Subgroup.mem_centralizer_singleton_iff.mp hp.2⟩
        have hRY := hirr _ hE2 inf_le_left hN2 fun hle => huE (hle hu2)
        rw [eq_bot_iff]
        intro x hx
        have hxR : x ∈ Subgroup.centralizer (R : Set G) :=
          Subgroup.mem_centralizer_iff.mpr fun r hr =>
            (Subgroup.mem_centralizer_iff.mp (hRY hr).2 x hx).symm
        exact Subgroup.mem_bot.mpr (hkill x hx.1.1 hx.1.2 hxR)
      let c : ↥(E ⊓ Subgroup.centralizer (L₀ : Set G)) →* G :=
        MonoidHom.mk' (fun f => (f : G) * u * (f : G)⁻¹ * u⁻¹) (by
          intro a b
          have ha := hEAZ a a.2.1 u huA
          have hb := hEAZ b b.2.1 u huA
          have hab : (a : G) * (b * u * (b : G)⁻¹ * u⁻¹) = (b * u * (b : G)⁻¹ * u⁻¹) * a :=
            (Subgroup.mem_centralizer_iff.mp (hEZ a.2.1) _ hb).symm
          have hzz := hEab _ (hVE (hZV hb)) _ (hVE (hZV ha))
          show (a : G) * b * u * ((a : G) * b)⁻¹ * u⁻¹ =
            (a : G) * u * (a : G)⁻¹ * u⁻¹ * ((b : G) * u * (b : G)⁻¹ * u⁻¹)
          calc (a : G) * b * u * ((a : G) * b)⁻¹ * u⁻¹
              = (a : G) * (b * u * (b : G)⁻¹ * u⁻¹) * (u * (a : G)⁻¹ * u⁻¹) := by group
            _ = (b * u * (b : G)⁻¹ * u⁻¹) * ((a : G) * u * (a : G)⁻¹ * u⁻¹) := by
                rw [hab]
                group
            _ = (a : G) * u * (a : G)⁻¹ * u⁻¹ * ((b : G) * u * (b : G)⁻¹ * u⁻¹) := hzz)
      have hcf : ∀ f, c f = (f : G) * u * (f : G)⁻¹ * u⁻¹ := fun f => rfl
      have hrange : c.range ≤ Z := by
        intro z hz
        obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hz
        exact hEAZ f f.2.1 u huA
      have hker : c.ker = ⊥ := by
        rw [eq_bot_iff]
        intro f hf
        rw [MonoidHom.mem_ker, hcf] at hf
        have hfu : (f : G) ∈ (E ⊓ Subgroup.centralizer (L₀ : Set G)) ⊓
            Subgroup.centralizer ({u} : Set G) := by
          refine ⟨f.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          calc (f : G) * u = ((f : G) * u * (f : G)⁻¹ * u⁻¹) * (u * f) := by group
            _ = u * f := by rw [hf, one_mul]
        rw [hFu] at hfu
        exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hfu))
      have hcardF : Nat.card ↥(E ⊓ Subgroup.centralizer (L₀ : Set G)) ≤ Nat.card Z := by
        have h1 := Subgroup.index_ker c
        rw [hker, Subgroup.index_bot] at h1
        rw [h1]
        exact Subgroup.card_le_of_le hrange
      calc V.relIndex E = V.relIndex (E ⊓ Subgroup.centralizer (L₀ : Set G) ⊔ V) := by
            rw [sup_comm, hdec]
        _ = V.relIndex (E ⊓ Subgroup.centralizer (L₀ : Set G)) :=
            relIndex_sup_eq_relIndex_of_le_normalizer hFNV
        _ ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (L₀ : Set G)) :=
            Nat.le_of_dvd Nat.card_pos
              (Subgroup.index_dvd_card (V.subgroupOf (E ⊓ Subgroup.centralizer (L₀ : Set G))))
        _ ≤ Nat.card Z := hcardF

end Core

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem lemma_6_1_26 (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h : Hyp6116 G T M L V n)
    (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G))
    (hRE : (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l).relIndex
        (pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
          conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l)) =
        2 ^ n * 2 ^ n) :
    ∀ e ∈ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l, e ∉ V →
      (∀ v ∈ V, ∃ r ∈ pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
          conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l),
          r * e * r⁻¹ = e * v) ∧
        V.relIndex (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
          conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l) ≤
          2 ^ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  obtain ⟨⟨-, -, hL1⟩, ⟨hRAB, -⟩, ⟨hEab, hEL1, -, hEN⟩, ⟨hRE', hABE, -⟩, -, -⟩ := h21
  obtain ⟨-, hidx24, -⟩ := h.lemma_6_1_24_two h432 h6111 h6119 hl hlN
  obtain ⟨hUO, hUOZ⟩ := h.lemma_6_1_20_one h432
  have hAU := (h.lemma_6_1_20_four h432 h6110 h6111 h6119).2.1
  obtain ⟨x, hxI, hne⟩ := h.exists_commutator_ne h432 h6111 h6119
  obtain ⟨hUW, -⟩ := h.le_sup_inf_centralizer h432 h6110 hxI hne
  have hWU : conjSub x V ≤ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
    Hyp6116.conjSub_le_conjClosure hxI
  have hxU := le_normalizer_conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) hxI
  have hVE := h.V_le_inf_conjSubgroup hl
  have hUS := h.conjClosure_le_S h432
  have hyp := h.almostSpecialL2Hyp h432 h6111 h6119
  have hUeq := h.conjClosure_normalizer_eq h432
  have hrc : ∀ X : Subgroup G, rconj X l = conjSubgroup X l := fun X => rfl
  have h6 := hyp.G23_six' (U := conjClosure V (Subgroup.normalizer (ch6ZS T L V : Set G)))
    rfl hl hlN rfl rfl rfl
  rw [hUeq, hrc] at h6
  obtain ⟨s, hsum⟩ := h6.1
  have hcardF : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (by have := h.two_le; omega)
  have h4 : 4 ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hlMV : l ∈ ch6MV M V := ⟨h.L_le hl, h.toHyp611.L_le_normalizer hl⟩
  have hLV := h.toHyp611.L_le_normalizer hl
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  set R := pCoreOf 2 (U ⊔ conjSubgroup U l) with hR
  set E := U ⊓ conjSubgroup U l with hE
  set A := U ⊓ Subgroup.centralizer (V : Set G) with hA
  set B := conjSubgroup U l ⊓ Subgroup.centralizer (V : Set G) with hB
  intro e heE heV
  have hEU : E ≤ U := inf_le_left
  have hAU' : A ≤ U := inf_le_left
  have hEA : E ≤ A := hABE ▸ inf_le_left
  have hAR : A ≤ R := hRAB ▸ le_sup_left
  have hBR : B ≤ R := hRAB ▸ le_sup_right
  have hRV : R ≤ Subgroup.centralizer (V : Set G) := by
    rw [hRAB]
    exact sup_le inf_le_right inf_le_right
  have hRL1 : R ≤ U ⊔ conjSubgroup U l := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hL1R : U ⊔ conjSubgroup U l ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hLL1 : L ≤ U ⊔ conjSubgroup U l := hL1 ▸ le_sup_left
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hEab ha hb
  have hAl : conjSub l⁻¹ A = B := by
    show conjSub l⁻¹ (U ⊓ Subgroup.centralizer (V : Set G)) =
      conjSub l⁻¹ U ⊓ Subgroup.centralizer (V : Set G)
    rw [conjSub_inf, conjSub_centralizer', conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ hLV)]
  have hL1le : U ⊔ conjSubgroup U l ≤ (conjSub x V ⊔ conjSub l⁻¹ (conjSub x V)) ⊔ R := by
    refine sup_le (hUW.trans (sup_le_sup le_sup_left hAR)) ?_
    have h1 : conjSub l⁻¹ U ≤ conjSub l⁻¹ (conjSub x V) ⊔ conjSub l⁻¹ A := by
      rw [← conjSub_sup]
      exact conjSub_mono l⁻¹ hUW
    rw [hAl] at h1
    exact h1.trans (sup_le_sup le_sup_right hBR)
  have hLle : L ≤ (conjSub x V ⊔ conjSub l⁻¹ (conjSub x V)) ⊔ R := hLL1.trans hL1le
  have hL₀L1 : conjSub x V ⊔ conjSub l⁻¹ (conjSub x V) ≤ U ⊔ conjSubgroup U l :=
    sup_le (hWU.trans le_sup_left) ((conjSub_mono l⁻¹ hWU).trans le_sup_right)
  have hL₀R : conjSub x V ⊔ conjSub l⁻¹ (conjSub x V) ≤ Subgroup.normalizer (R : Set G) :=
    hL₀L1.trans hL1R
  have hEl : conjSub l⁻¹ E = E := conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ (hEN hlMV))
  have hxU' : conjSub x U = U := conjSub_eq_of_mem_normalizer' hxU
  have hCW : (Subgroup.centralizer (conjSub x V : Set G)).relIndex E ≤ 2 ^ n := by
    have e1 : conjSub x A = U ⊓ Subgroup.centralizer (conjSub x V : Set G) := by
      show conjSub x (U ⊓ Subgroup.centralizer (V : Set G)) = _
      rw [conjSub_inf, hxU', conjSub_centralizer']
    have e2 : (U ⊓ Subgroup.centralizer (conjSub x V : Set G)).relIndex U = 2 ^ n := by
      have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj x).toMonoidHom) A U
        (MulAut.conj x).injective
      change (conjSub x A).relIndex (conjSub x U) = A.relIndex U at this
      rw [e1, hxU', hAU] at this
      exact this
    calc (Subgroup.centralizer (conjSub x V : Set G)).relIndex E
        ≤ (Subgroup.centralizer (conjSub x V : Set G)).relIndex U :=
          Subgroup.relIndex_le_of_le_right hEU (relIndex_ne_zero' U _)
      _ = (U ⊓ Subgroup.centralizer (conjSub x V : Set G)).relIndex U :=
          (Subgroup.inf_relIndex_left U _).symm
      _ = 2 ^ n := e2
  have hCW' : (Subgroup.centralizer (conjSub l⁻¹ (conjSub x V) : Set G)).relIndex E ≤ 2 ^ n := by
    have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj l⁻¹).toMonoidHom)
      (Subgroup.centralizer (conjSub x V : Set G)) E (MulAut.conj l⁻¹).injective
    change (conjSub l⁻¹ (Subgroup.centralizer (conjSub x V : Set G))).relIndex
      (conjSub l⁻¹ E) = _ at this
    rw [conjSub_centralizer', hEl] at this
    rw [this]
    exact hCW
  have hidxF : (E ⊓ Subgroup.centralizer
      ((conjSub x V ⊔ conjSub l⁻¹ (conjSub x V) : Subgroup G) : Set G)).relIndex E ≤
      Nat.card V := by
    have hle : E ⊓ Subgroup.centralizer (conjSub x V : Set G) ⊓
        Subgroup.centralizer (conjSub l⁻¹ (conjSub x V) : Set G) ≤
        E ⊓ Subgroup.centralizer
          ((conjSub x V ⊔ conjSub l⁻¹ (conjSub x V) : Subgroup G) : Set G) :=
      fun y hy => ⟨hy.1.1, mem_centralizer_sup hy.1.2 hy.2⟩
    calc (E ⊓ Subgroup.centralizer
          ((conjSub x V ⊔ conjSub l⁻¹ (conjSub x V) : Subgroup G) : Set G)).relIndex E
        ≤ (E ⊓ Subgroup.centralizer (conjSub x V : Set G) ⊓
            Subgroup.centralizer (conjSub l⁻¹ (conjSub x V) : Set G)).relIndex E :=
          Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero' E _)
      _ ≤ (E ⊓ Subgroup.centralizer (conjSub x V : Set G)).relIndex E *
            (Subgroup.centralizer (conjSub l⁻¹ (conjSub x V) : Set G)).relIndex E :=
          Subgroup.relIndex_inf_le
      _ = (Subgroup.centralizer (conjSub x V : Set G)).relIndex E *
            (Subgroup.centralizer (conjSub l⁻¹ (conjSub x V) : Set G)).relIndex E := by
          rw [Subgroup.inf_relIndex_left]
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hCW hCW'
      _ = Nat.card V := h.toHyp611Nat.natural.card_eq.symm
  have hCL : E ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hCTL]
    exact inf_le_inf_right _ ((hEU.trans hUS).trans inf_le_left)
  have hVF : V ⊓ (E ⊓ Subgroup.centralizer
      ((conjSub x V ⊔ conjSub l⁻¹ (conjSub x V) : Subgroup G) : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_centralizer_of_le_sup hLle hCL hy.2.1 hy.2.2
      (Subgroup.mem_centralizer_iff.mpr fun r hr =>
        (Subgroup.mem_centralizer_iff.mp (hRV hr) y hy.1).symm))
  have hdec : V ⊔ (E ⊓ Subgroup.centralizer
      ((conjSub x V ⊔ conjSub l⁻¹ (conjSub x V) : Subgroup G) : Set G)) = E :=
    sup_eq_of_relIndex_le_card hVE inf_le_left hEcomm hVF hidxF
  have hs : s = 1 := by
    have h1 := relIndex_eq_of_sumNatural hsum
    rw [hcardF, hRE] at h1
    have h3 : ((2 ^ n) ^ 2) ^ s = ((2 ^ n) ^ 2) ^ 1 := by rw [← h1, pow_one, sq]
    have h2 : 2 ≤ (2 ^ n) ^ 2 :=
      le_trans (by omega : 2 ≤ 2 ^ n) (Nat.le_self_pow two_ne_zero _)
    exact Nat.pow_right_injective h2 h3
  subst hs
  have hirr : ∀ Y : Subgroup G, E ≤ Y → Y ≤ R →
      (conjSub x V ⊔ conjSub l⁻¹ (conjSub x V)) ⊔ R ≤ Subgroup.normalizer (Y : Set G) →
      ¬ Y ≤ E → R ≤ Y := fun Y hEY hYR hN hY =>
    le_of_sumNatural_one hsum hEY hYR (hL1le.trans hN) hY
  have hAE : ¬ A ≤ E := by
    intro hle
    have hAeq : A = E := le_antisymm hle hEA
    rw [hAeq, hRE] at hidx24
    have hm : 2 ^ n * 2 ^ n = 1 := by
      have hpos : 0 < 2 ^ n * 2 ^ n := by positivity
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hidx24)
    have h16 := Nat.mul_le_mul h4 h4
    rw [hm] at h16
    omega
  have hEZ : E ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := fun y hy =>
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ (hUO (hEU hy))
  have hER : ∀ a ∈ E, ∀ r ∈ R, a⁻¹ * r * a * r⁻¹ ∈ V := by
    intro a ha r hr
    have := hEL1 (Subgroup.commutator_mem_commutator (E.inv_mem ha) (hRL1 hr))
    rwa [commutatorElement_def, inv_inv] at this
  have hEAZ : ∀ a ∈ E, ∀ u ∈ A, a * u * a⁻¹ * u⁻¹ ∈ ch6ZS T L V := by
    intro a ha u hu
    have := hUOZ (Subgroup.commutator_mem_commutator (hEU ha) (hUO (hAU' hu)))
    rwa [commutatorElement_def] at this
  have hcore := lemma_6_1_26_core hVE hEA hAR hAE (inf_le_left : ch6ZS T L V ≤ V) hEcomm hEZ
    hER hRV (fun r hr s hs => (hRE' r hr s hs).1) hEAZ hL₀R hLle hirr
    (fun P hPV hLP => h.toHyp611Nat.natural.irreducible P hPV hLP) hCL hdec
  rw [h.toHyp611Nat.card_ZS] at hcore
  exact ⟨hcore.1 e heE heV, hcore.2⟩

end Hyp6116

theorem stmt6_1_26 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19) (h6125 : Stmt6_1_25) :
    Stmt6_1_26 := by
  intro G _ _ T M L V n h l hl hlN
  dsimp only
  intro e he heV
  have h25 := h6125 G T M L V n h l hl hlN
  dsimp only at h25
  obtain ⟨hn2, -, hRE⟩ := h25
  have h26 := h.lemma_6_1_26 h432 h6110 h6111 h6119
    (h.toHyp611.inf_centralizer_eq_bot h331 h432 h615) hl hlN hRE e he heV
  subst hn2
  exact ⟨h26.1, h26.2.trans (by norm_num)⟩

end CFSG.Quasithin.H13
