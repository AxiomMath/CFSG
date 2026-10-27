module

public import CFSG.Quasithin.Background.C41PfKG
public import CFSG.Quasithin.Background.C48SporSetup
public import CFSG.Quasithin.Background.A1cA132Struct
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.HomocyclicFrattini

public section

namespace CFSG.Quasithin.C213NonQ

variable {G : Type} [Group G]

theorem mem_centralizer_of_two_pow [Finite G] {K F : Subgroup G} {r : G}
    (hKF : K ≤ Subgroup.normalizer (F : Set G))
    (hC : K ⊓ Subgroup.centralizer (F : Set G) ≤ F) (hF : Odd (Nat.card F))
    (hrK : r ∈ Subgroup.normalizer (K : Set G)) (hrF : r ∈ Subgroup.centralizer (F : Set G))
    {n : ℕ} (hr : r ^ 2 ^ n = 1) : r ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hrkK : r * k * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hrK k).mp hk
  set d := k⁻¹ * (r * k * r⁻¹) with hd
  have hdK : d ∈ K := K.mul_mem (K.inv_mem hk) hrkK
  have hdC : d ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hkf : k * f * k⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (hKF hk) f).mp hf
    have e1 : r⁻¹ * f * r = f := by
      have := Subgroup.mem_centralizer_iff.mp hrF f hf
      rw [mul_assoc, this, inv_mul_cancel_left]
    have e2 : r * (k * f * k⁻¹) * r⁻¹ = k * f * k⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp hrF _ hkf
      rw [← this, mul_inv_cancel_right]
    have h3 : d * f * d⁻¹ = f := by
      calc d * f * d⁻¹ = k⁻¹ * r * k * (r⁻¹ * f * r) * k⁻¹ * r⁻¹ * k := by rw [hd]; group
        _ = k⁻¹ * (r * (k * f * k⁻¹) * r⁻¹) * k := by rw [e1]; group
        _ = f := by rw [e2]; group
    calc f * d = d * f * d⁻¹ * d := by rw [h3]
      _ = d * f := by group
  have hdF : d ∈ F := hC ⟨hdK, hdC⟩
  have hrd : r * d * r⁻¹ = d := by
    have := Subgroup.mem_centralizer_iff.mp hrF d hdF
    rw [← this, mul_inv_cancel_right]
  have hpow : ∀ m : ℕ, r ^ m * k * (r ^ m)⁻¹ = k * d ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hrk : r * k * r⁻¹ = k * d := by rw [hd]; group
      calc r ^ (m + 1) * k * (r ^ (m + 1))⁻¹ = r * (r ^ m * k * (r ^ m)⁻¹) * r⁻¹ := by group
        _ = r * k * r⁻¹ * (r * d * r⁻¹) ^ m := by rw [ih, conj_pow]; group
        _ = k * d ^ (m + 1) := by rw [hrk, hrd, pow_succ', mul_assoc]
  have hd2 : d ^ 2 ^ n = 1 := by
    have := hpow (2 ^ n)
    rw [hr, one_mul, inv_one, mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hd1 : d = 1 := by
    have h1 : orderOf d ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hd2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have h2 : orderOf d ∣ Nat.card F := by
      have := orderOf_dvd_natCard (⟨d, hdF⟩ : ↥F)
      rwa [Subgroup.orderOf_mk] at this
    rcases j with _ | j
    · exact orderOf_eq_one_iff.mp (by simpa using hj)
    · exfalso
      rw [hj] at h2
      obtain ⟨c, hc⟩ := hF
      have : 2 ∣ Nat.card F := (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2
      omega
  have : r * k * r⁻¹ = k := by
    have := hd1
    rw [hd, inv_mul_eq_one] at this
    exact this.symm
  calc k * r = r * k * r⁻¹ * r := by rw [this]
    _ = r * k := by group

theorem commutator_eq_of_card_sq [Finite G] {p : ℕ} (hp : p.Prime) {F L : Subgroup G}
    (hF : Nat.card F = p ^ 2) (hLF : L ≤ Subgroup.normalizer (F : Set G)) (hL : ⁅L, L⁆ = L)
    (hne : ⁅F, L⁆ ≠ ⊥) : ⁅F, L⁆ = F := by
  have : Fact p.Prime := ⟨hp⟩
  have hCF : ⁅F, L⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro f hf l hl
    have h1 : l * f⁻¹ * l⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (hLF hl) f⁻¹).mp (F.inv_mem hf)
    rw [commutatorElement_def, show f * l * f⁻¹ * l⁻¹ = f * (l * f⁻¹ * l⁻¹) by group]
    exact F.mul_mem hf h1
  have hdvd : Nat.card ↥⁅F, L⁆ ∣ p ^ 2 := hF ▸ Subgroup.card_dvd_of_le hCF
  obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases j
  · exact absurd (Subgroup.eq_bot_of_card_eq _ (by simpa using hj)) hne
  · exfalso
    have hLC : L ≤ Subgroup.normalizer ((⁅F, L⁆ : Subgroup G) : Set G) :=
      C48Spor.le_normalizer_commutator_right' F L
    have hcyc : IsCyclic ↥⁅F, L⁆ := isCyclic_of_prime_card (by simpa using hj)
    set ψ : ↥L →* MulAut ↥⁅F, L⁆ :=
      (Subgroup.normalizerMonoidHom ⁅F, L⁆).comp (Subgroup.inclusion hLC) with hψ
    have hcomm : ∀ a b : MulAut ↥⁅F, L⁆, a * b = b * a := fun a b =>
      (IsCyclic.mulAutMulEquiv ↥⁅F, L⁆).injective (by rw [map_mul, map_mul, mul_comm])
    have hrange : ψ.range = ⊥ := by
      refine C41Pf.eq_bot_of_perfect_of_isSolvable ?_ ?_
      · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
        congr 1
        apply Subgroup.map_injective L.subtype_injective
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hL]
      · have : IsMulCommutative ↥ψ.range :=
          ⟨⟨fun a b => Subtype.ext (hcomm a.1 b.1)⟩⟩
        infer_instance
    have hC1 : ⁅⁅F, L⁆, L⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro c hc l hl
      have h1 : ψ ⟨l, hl⟩ = 1 := by
        have : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨_, rfl⟩
        rw [hrange] at this
        exact Subgroup.mem_bot.mp this
      have h2 := congrArg (fun φ : MulAut ↥⁅F, L⁆ => ((φ ⟨c, hc⟩ : ↥⁅F, L⁆) : G)) h1
      simp only [hψ, MonoidHom.comp_apply, MulAut.one_apply] at h2
      change l * c * l⁻¹ = c at h2
      rw [Subgroup.mem_bot, commutatorElement_def]
      calc c * l * c⁻¹ * l⁻¹ = c * (l * c * l⁻¹)⁻¹ := by group
        _ = 1 := by rw [h2, mul_inv_cancel]
    have hLLF : ⁅⁅L, L⁆, F⁆ = ⊥ := by
      refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
      · rw [Subgroup.commutator_comm L F]
        exact hC1
      · exact hC1
    rw [hL, Subgroup.commutator_comm] at hLLF
    exact hne hLLF
  · exact Subgroup.eq_of_le_of_card_ge hCF (by rw [hF, hj])

open CFSG.SectionRank.Ccomm in
theorem commutator_eq_bot_of_le_frattini [Finite G] {q : ℕ} [Fact q.Prime] {P L : Subgroup G}
    (hP : IsPGroup q ↥P) (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hL : ⁅L, L⁆ = L)
    (hΦ : ⁅P, L⁆ ≤ (frattini ↥P).map P.subtype) : ⁅P, L⁆ = ⊥ := by
  set ψ : ↥L →* MulAut ↥P := (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hLP)
    with hψ
  have hψapp : ∀ (l : ↥L) (x : ↥P), ((ψ l x : ↥P) : G) = l * x * (l : G)⁻¹ := fun l x => rfl
  have hker : ψ.range ≤ (autQuotient (frattini ↥P)).ker := by
    rintro _ ⟨l, rfl⟩
    rw [mem_ker_autQuotient]
    intro x
    have h1 : (x : G)⁻¹ * (l * x * (l : G)⁻¹) ∈ ⁅P, L⁆ := by
      have := Subgroup.commutator_mem_commutator (P.inv_mem x.2) l.2
      rw [commutatorElement_def, inv_inv] at this
      convert this using 1
      group
    obtain ⟨y, hy, hyx⟩ := hΦ h1
    have h2 : x⁻¹ * ψ l x = y := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hψapp]
      exact hyx.symm)
    rw [h2]
    exact hy
  have hq : IsPGroup q ↥(autQuotient (frattini ↥P)).ker := isPGroup_ker_autQuotient_frattini hP
  have hrange : ψ.range = ⊥ := by
    refine C41Pf.eq_bot_of_perfect_of_isSolvable ?_ ?_
    · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective L.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hL]
    · have h3 : IsPGroup q ↥ψ.range := hq.to_le hker
      have : Group.IsNilpotent ↥ψ.range := h3.isNilpotent
      infer_instance
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx l hl
  have h1 : ψ ⟨l, hl⟩ = 1 := by
    have : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨_, rfl⟩
    rwa [hrange, Subgroup.mem_bot] at this
  have h2 := congrArg (fun φ : MulAut ↥P => ((φ ⟨x, hx⟩ : ↥P) : G)) h1
  simp only [MulAut.one_apply] at h2
  rw [hψapp] at h2
  rw [Subgroup.mem_bot, commutatorElement_def]
  calc x * l * x⁻¹ * l⁻¹ = x * (l * x * l⁻¹)⁻¹ := by group
    _ = 1 := by rw [h2, mul_inv_cancel]

theorem commutator_eq_or_eq_bot [Finite G] {q : ℕ} [Fact q.Prime] {P L : Subgroup G}
    (hP : IsPGroup q ↥P) (hPΦ : Nat.card (↥P ⧸ frattini ↥P) = q ^ 2)
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hL : ⁅L, L⁆ = L) :
    ⁅P, L⁆ = ⊥ ∨ ⁅P, L⁆ = P := by
  classical
  set Φ : Subgroup G := (frattini ↥P).map P.subtype with hΦdef
  have hΦP : Φ ≤ P := Subgroup.map_subtype_le _
  set X := P ⊔ L with hX
  have hPX : P ≤ X := le_sup_left
  have hLX : L ≤ X := le_sup_right
  have hconj : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ y ∈ Φ, g * y * g⁻¹ ∈ Φ := by
    intro g hg y hy
    obtain ⟨y', hy', rfl⟩ := hy
    set α : MulAut ↥P := Subgroup.normalizerMonoidHom P ⟨g, hg⟩ with hα
    have h1 : α y' ∈ frattini ↥P := by
      have := (inferInstance : (frattini ↥P).Characteristic)
      rw [Subgroup.characteristic_iff_map_le] at this
      exact this α ⟨y', hy', rfl⟩
    exact ⟨α y', h1, rfl⟩
  have hΦn : X ≤ Subgroup.normalizer (Φ : Set G) := by
    have hle : X ≤ Subgroup.normalizer (P : Set G) :=
      sup_le Subgroup.le_normalizer hLP
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj g (hle hg) y, fun hy => ?_⟩
    have := hconj g⁻¹ (Subgroup.inv_mem _ (hle hg)) _ hy
    simpa [mul_assoc] using this
  set N : Subgroup ↥X := Φ.subgroupOf X with hN
  have : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (hΦP.trans hPX)).mpr hΦn
  set π := QuotientGroup.mk' N with hπ
  set Pb := (P.subgroupOf X).map π with hPb
  set Lb := (L.subgroupOf X).map π with hLb
  set ρ : ↥P →* ↥X ⧸ N := π.comp (Subgroup.inclusion hPX) with hρ
  have hρker : ρ.ker = frattini ↥P := by
    ext x
    rw [MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hρrange : ρ.range = Pb := by
    rw [hPb, hρ, MonoidHom.range_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hcardPb : Nat.card Pb = q ^ 2 := by
    rw [← hρrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← hPΦ]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hρker).toEquiv
  have hLPb : Lb ≤ Subgroup.normalizer (Pb : Set (↥X ⧸ N)) := by
    rw [hLb, hPb]
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map π)
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hLP hl) x
  have hLbp : ⁅Lb, Lb⁆ = Lb := by
    rw [hLb, ← Subgroup.map_commutator, ← C48Spor.commutator_subgroupOf_of_le hLX hLX, hL]
  have hcomm : ⁅Pb, Lb⁆ = ((⁅P, L⁆).subgroupOf X).map π := by
    rw [hPb, hLb, ← Subgroup.map_commutator, ← C48Spor.commutator_subgroupOf_of_le hPX hLX]
  have hcPL : ⁅P, L⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have h1 : l * x⁻¹ * l⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hLP hl) x⁻¹).mp (P.inv_mem hx)
    rw [commutatorElement_def, show x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) by group]
    exact P.mul_mem hx h1
  by_cases hne : ⁅Pb, Lb⁆ = ⊥
  · left
    refine commutator_eq_bot_of_le_frattini hP hLP hL fun c hc => ?_
    have h1 : π ⟨c, (hcPL.trans hPX) hc⟩ ∈ ⁅Pb, Lb⁆ := by
      rw [hcomm]
      exact ⟨_, hc, rfl⟩
    rw [hne, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · right
    have h1 := commutator_eq_of_card_sq (Fact.out : q.Prime) hcardPb hLPb hLbp hne
    have h2 : (⁅P, L⁆).subgroupOf P ⊔ frattini ↥P = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : π ⟨x, hPX x.2⟩ ∈ ⁅Pb, Lb⁆ := by
        rw [h1]
        exact ⟨_, x.2, rfl⟩
      rw [hcomm] at hx
      obtain ⟨c, hc, hcx⟩ := hx
      have hcx' : c⁻¹ * ⟨x, hPX x.2⟩ ∈ N := QuotientGroup.eq.mp hcx
      obtain ⟨y, hy, hyx⟩ := hcx'
      have hcP : (c : G) ∈ P := hcPL hc
      have hxe : x = ⟨c, hcP⟩ * y := Subtype.ext (by
        have : (y : G) = (c : G)⁻¹ * x := hyx
        rw [Subgroup.coe_mul, this]
        group)
      rw [hxe]
      exact Subgroup.mul_mem_sup (show (⟨c, hcP⟩ : ↥P) ∈ (⁅P, L⁆).subgroupOf P from hc) hy
    have h3 := frattini_nongenerating h2
    apply le_antisymm hcPL
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ (⁅P, L⁆).subgroupOf P := by rw [h3]; trivial
    exact this

theorem card_frattini_quotient_of_isPOnePlusTwo {q : ℕ} [Fact q.Prime] {X : Type*} [Group X]
    [Finite X] (hX : IsPOnePlusTwo q X) : Nat.card (X ⧸ frattini X) = q ^ 2 := by
  have hfr := A1c.frattini_eq_center_of_isPOnePlusTwo hX
  obtain ⟨hext, hcard, -⟩ := hX
  have := hext
  have hZ := CFSG.IsExtraspecial.center_order_p q X
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini X)
  rw [hfr, hZ, hcard] at h1
  rw [hfr]
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have : q ^ 3 = q ^ 2 * q := by ring
  rw [this] at h1
  exact (Nat.eq_of_mul_eq_mul_right hq h1).symm

theorem card_frattini_quotient_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (X ⧸ frattini X) = Nat.card (Y ⧸ frattini Y) := by
  have h : (frattini X).map e.toMonoidHom = frattini Y := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective
    · intro y hy
      refine ⟨e.symm y, ?_, by simp⟩
      exact frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective
        hy
  exact Nat.card_congr (QuotientGroup.congr _ _ e h).toEquiv

theorem card_frattini_quotient_of_isHomocyclicRank2 {q : ℕ} [Fact q.Prime] {X : Type} [Group X]
    (hX : IsHomocyclicRank2 q X) : Nat.card (X ⧸ frattini X) = q ^ 2 := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hX
  let g : (Fin 2 → Multiplicative (ZMod (q ^ n))) ≃*
      Multiplicative (ZMod (q ^ n)) × Multiplicative (ZMod (q ^ n)) :=
    { piFinTwoEquiv (fun _ => Multiplicative (ZMod (q ^ n))) with map_mul' := fun _ _ => rfl }
  set f : Multiplicative (ZMod (q ^ n)) × Multiplicative (ZMod (q ^ n)) ≃*
      CFSG.StandardHomocyclicCover (Fin 2) (q ^ n) :=
    g.symm.trans (MulEquiv.piMultiplicative fun _ : Fin 2 => ZMod (q ^ n)).symm with hf
  rw [card_frattini_quotient_congr (e.trans f),
    Nat.card_congr (CFSG.standardHomocyclicCoverFrattiniQuotientEquiv (Fin 2) q n hn).toEquiv,
    Nat.card_eq_fintype_card]
  simp [CFSG.StandardHomocyclicCover, ZMod.card]

end CFSG.Quasithin.C213NonQ
