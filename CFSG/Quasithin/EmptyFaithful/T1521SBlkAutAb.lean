module

public import CFSG.Quasithin.EmptyFaithful.T1521SBlkThree
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section Fix

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_sdiff_commutator_mem1521 {U Z : Subgroup G} {v : G}
    (hU2 : IsPGroup 2 U) (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hZU : Z < U)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G)) (hvU : v ∈ Subgroup.normalizer (U : Set G))
    (hvZ : v ∈ Subgroup.normalizer (Z : Set G)) :
    ∃ u ∈ U, u ∉ Z ∧ v * u * v⁻¹ * u⁻¹ ∈ Z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := Subgroup.zpowers v with hV
  set R : Subgroup G := U ⊔ V with hR
  have hUR : U ≤ R := le_sup_left
  have hVR : V ≤ R := le_sup_right
  have hvR : v ∈ R := hVR (Subgroup.mem_zpowers v)
  have hRU : R ≤ Subgroup.normalizer (U : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hvU)
  have hRZ : R ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le hUN (Subgroup.zpowers_le.mpr hvZ)
  have hR2 : IsPGroup 2 R := hU2.to_sup_of_normal_left' hv2 (Subgroup.zpowers_le.mpr hvU)
  have hZR : Z ≤ R := hZU.le.trans hUR
  have hZn : (Z.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZR).mpr hRZ
  have hUn : (U.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUR).mpr hRU
  have hnil : Group.IsNilpotent (↥R ⧸ Z.subgroupOf R) :=
    (hR2.to_quotient (Z.subgroupOf R)).isNilpotent
  set N : Subgroup (↥R ⧸ Z.subgroupOf R) :=
    (U.subgroupOf R).map (QuotientGroup.mk' (Z.subgroupOf R)) with hN
  have hNn : N.Normal := Subgroup.Normal.map hUn _ (QuotientGroup.mk'_surjective _)
  obtain ⟨u₀, hu₀U, hu₀Z⟩ := IsConcreteLE.exists_of_lt hZU
  have hNne : N ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' (Z.subgroupOf R) ⟨u₀, hUR hu₀U⟩ ∈ N :=
      ⟨⟨u₀, hUR hu₀U⟩, Subgroup.mem_subgroupOf.mpr hu₀U, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hu₀Z hmem
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := N) hNne
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨y, hy, hyx⟩ := x.2.1
  have hxc := Subgroup.mem_center_iff.mp x.2.2 (QuotientGroup.mk' (Z.subgroupOf R) ⟨v, hvR⟩)
  have huU : (y : G) ∈ U := Subgroup.mem_subgroupOf.mp hy
  refine ⟨y, huU, ?_, ?_⟩
  · intro hyZ
    apply hx1
    apply Subtype.ext
    rw [← hyx]
    show QuotientGroup.mk' (Z.subgroupOf R) y = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hyZ
  · rw [← hyx] at hxc
    have h2 : (QuotientGroup.mk' (Z.subgroupOf R) (⟨v, hvR⟩ * y)) =
        (QuotientGroup.mk' (Z.subgroupOf R) (y * ⟨v, hvR⟩)) := by
      rw [map_mul, map_mul]; exact hxc
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    have h3 : (y : G)⁻¹ * (v : G)⁻¹ * y * v ∈ Z := by
      have := Subgroup.mem_subgroupOf.mp h2
      simpa [mul_assoc] using this
    have hyR : (y : G) ∈ R := y.2
    have h4 := (Subgroup.mem_normalizer_iff.mp (hRZ (R.mul_mem hvR hyR)) _).mp h3
    have e : v * (y : G) * ((y : G)⁻¹ * (v : G)⁻¹ * y * v) * (v * (y : G))⁻¹ =
        (y : G) * v * (y : G)⁻¹ * v⁻¹ := by group
    rw [e] at h4
    have h5 := Z.inv_mem h4
    have e2 : ((y : G) * v * (y : G)⁻¹ * v⁻¹)⁻¹ = v * (y : G) * v⁻¹ * (y : G)⁻¹ := by group
    rwa [e2] at h5

end Fix

section Ab1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_forall_conj_mem1521 {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K) : H ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => h x hx k hk, fun hk => ?_⟩
  have := h x⁻¹ (H.inv_mem hx) _ hk
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_centralizer1521 {L : Subgroup G} {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G)) :
    v ∈ Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ z ∈ Subgroup.centralizer (L : Set G),
      g * z * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro g hg z hz
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
      simpa using this
    have h2 := Subgroup.mem_centralizer_iff.mp hz _ h1
    calc l * (g * z * g⁻¹) = g * ((g⁻¹ * l * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * l * g)) * g⁻¹ := by rw [h2]
      _ = g * z * g⁻¹ * l := by group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key v hv z, fun hz => ?_⟩
  have := key v⁻¹ (Subgroup.inv_mem _ hv) _ hz
  simpa [mul_assoc] using this


omit [Finite G] in
theorem isPGroup_of_exp_two1521 {U : Subgroup G} (hU2 : ∀ x ∈ U, x ^ 2 = 1) : IsPGroup 2 ↥U := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using hU2 x x.2

theorem block_centralizes_aux1521 {L Q U Z : Subgroup G} {v : G}
    (hLL : ⁅L, L⁆ = L) (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hUdef : ⁅Q, L⁆ = U) (hUc : ∀ x ∈ U, ∀ q ∈ Q, x * q = q * x) (hU2 : ∀ x ∈ U, x ^ 2 = 1)
    (hZdef : Z = U ⊓ Subgroup.centralizer (L : Set G)) (hZU : Z < U)
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ U → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = U)
    (hvL : v ∈ Subgroup.normalizer (L : Set G)) (hvQ : v ∈ Subgroup.normalizer (Q : Set G))
    (hv2 : IsPGroup 2 ↥(Subgroup.zpowers v)) (hA : ∀ l ∈ L, ⁅l, v⁆ ∈ Q) :
    (∀ l ∈ L, ⁅l, v⁆ ∈ U) ∧ (∀ u ∈ U, v * u = u * v) ∧ (∀ q ∈ Q, ⁅q, v⁆ ∈ Z) := by
  have hUQ : U ≤ Q := by
    rw [← hUdef]; exact Subgroup.le_normalizer_iff_commutator_le_left.mp hLQ
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := by
    rw [← hUdef]; exact Subgroup.normalizer_commutator_ge_right Q L
  have hvU : v ∈ Subgroup.normalizer (U : Set G) := by
    rw [← hUdef]; exact A4.mem_normalizer_commutator hvQ hvL
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy => hUc x hx y (hUQ hy)
  have hZmem : ∀ z, z ∈ Z ↔ z ∈ U ∧ ∀ l ∈ L, l * z = z * l := by
    intro z; rw [hZdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]; exact Iff.rfl
  have hZU' : Z ≤ U := hZU.le
  have hZcent : ∀ z ∈ Z, ∀ l ∈ L, l * z * l⁻¹ = z := by
    intro z hz l hl
    rw [(hZmem z).1 hz |>.2 l hl]; group
  have hvZ : v ∈ Subgroup.normalizer (Z : Set G) := by
    rw [hZdef]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hvU, mem_normalizer_centralizer1521 hvL⟩
  have hUZn : U ≤ Subgroup.normalizer (Z : Set G) := by
    refine le_normalizer_of_forall_conj_mem1521 fun u hu z hz => ?_
    have : u * z * u⁻¹ = z := by
      rw [hUcomm u hu z (hZU' hz)]; group
    rw [this]; exact hz
  have hLZn : L ≤ Subgroup.normalizer (Z : Set G) := by
    refine le_normalizer_of_forall_conj_mem1521 fun l hl z hz => ?_
    rw [hZcent z hz l hl]; exact hz
  let Cv : Subgroup G :=
    { carrier := {w | w ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ l ∈ L, ⁅l, w⁆ ∈ Q}
      one_mem' := ⟨Subgroup.one_mem _, fun l _ => by simp⟩
      mul_mem' := fun {w₁ w₂} h₁ h₂ => ⟨Subgroup.mul_mem _ h₁.1 h₂.1, fun l hl => by
        have e : ⁅l, w₁ * w₂⁆ = ⁅l, w₁⁆ * (w₁ * ⁅l, w₂⁆ * w₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Q.mul_mem (h₁.2 l hl) ((Subgroup.mem_normalizer_iff.mp h₁.1 _).mp (h₂.2 l hl))⟩
      inv_mem' := fun {w} h => ⟨Subgroup.inv_mem _ h.1, fun l hl => by
        have e : ⁅l, w⁻¹⁆ = w⁻¹ * (⁅l, w⁆)⁻¹ * w := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h.1) _).mp
          (Q.inv_mem (h.2 l hl))
        simpa using h1⟩ }
  have hAv : Subgroup.zpowers v ≤ Cv := Subgroup.zpowers_le.mpr ⟨hvQ, hA⟩
  have hLV : ⁅L, Subgroup.zpowers v⁆ ≤ Q :=
    Subgroup.commutator_le.mpr fun l hl w hw => (hAv hw).2 l hl
  have hA' : ⁅L, Subgroup.zpowers v⁆ ≤ U := by
    have h3 := commutator_commutator_le_of_rotate1521 (N := U) (H₁ := L) (H₂ := L)
      (H₃ := Subgroup.zpowers v) hLU hLU (Subgroup.zpowers_le.mpr hvU)
      (by rw [← hUdef]; exact Subgroup.commutator_mono hLV le_rfl)
      (by rw [← hUdef, Subgroup.commutator_comm (Subgroup.zpowers v) L];
          exact Subgroup.commutator_mono hLV le_rfl)
    rwa [hLL] at h3
  have hAU : ∀ l ∈ L, ⁅l, v⁆ ∈ U := fun l hl =>
    hA' (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers v))
  have hequiv : ∀ l ∈ L, ∀ u ∈ U, v * (l * u * l⁻¹) * v⁻¹ = l * (v * u * v⁻¹) * l⁻¹ := by
    intro l hl u hu
    have hq : ⁅l, v⁆ ∈ U := hAU l hl
    have hvu : v * u * v⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hvU u).mp hu
    have hx : l * (v * u * v⁻¹) * l⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hLU hl) _).mp hvu
    have hc : l * (v * u * v⁻¹) * l⁻¹ * ⁅l, v⁆ = ⁅l, v⁆ * (l * (v * u * v⁻¹) * l⁻¹) :=
      hUc _ hx _ (hUQ hq)
    have e : v * (l * u * l⁻¹) * v⁻¹ =
        (⁅l, v⁆)⁻¹ * (l * (v * u * v⁻¹) * l⁻¹) * ⁅l, v⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, mul_assoc, hc, inv_mul_cancel_left]
  let W : Subgroup G :=
    { carrier := {u | u ∈ U ∧ v * u * v⁻¹ * u⁻¹ ∈ Z}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := fun {u u'} h h' => by
        refine ⟨U.mul_mem h.1 h'.1, ?_⟩
        have e : v * (u * u') * v⁻¹ * (u * u')⁻¹ =
            (v * u * v⁻¹ * u⁻¹) * (u * (v * u' * v⁻¹ * u'⁻¹) * u⁻¹) := by group
        rw [e]
        refine Z.mul_mem h.2 ?_
        have hz : v * u' * v⁻¹ * u'⁻¹ ∈ U := hZU' h'.2
        have : u * (v * u' * v⁻¹ * u'⁻¹) * u⁻¹ = v * u' * v⁻¹ * u'⁻¹ := by
          rw [hUcomm u h.1 _ hz]; group
        rw [this]; exact h'.2
      inv_mem' := fun {u} h => by
        refine ⟨U.inv_mem h.1, ?_⟩
        have e : v * u⁻¹ * v⁻¹ * (u⁻¹)⁻¹ = u⁻¹ * (v * u * v⁻¹ * u⁻¹)⁻¹ * u := by group
        rw [e]
        have hz : v * u * v⁻¹ * u⁻¹ ∈ U := hZU' h.2
        have : u⁻¹ * (v * u * v⁻¹ * u⁻¹)⁻¹ * u = (v * u * v⁻¹ * u⁻¹)⁻¹ := by
          have hc := hUcomm u⁻¹ (U.inv_mem h.1) _ (U.inv_mem hz)
          rw [hc]; group
        rw [this]; exact Z.inv_mem h.2 }
  have hZW : Z ≤ W := by
    intro z hz
    refine ⟨hZU' hz, ?_⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hvZ z).mp hz
    exact Z.mul_mem h1 (Z.inv_mem hz)
  have hWU : W ≤ U := fun u hu => hu.1
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_forall_conj_mem1521 fun l hl u hu => ?_
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hLU hl) u).mp hu.1, ?_⟩
    have hu' : u ∈ U := hu.1
    have h1 := hequiv l hl u hu'
    have e : v * (l * u * l⁻¹) * v⁻¹ * (l * u * l⁻¹)⁻¹ =
        l * (v * u * v⁻¹ * u⁻¹) * l⁻¹ := by
      rw [h1]; group
    rw [e, hZcent _ hu.2 l hl]
    exact hu.2
  have hWU' : W = U := by
    rcases hirr W hZW hWU hLW with h | h
    · exfalso
      obtain ⟨u, huU, huZ, hu⟩ := exists_mem_sdiff_commutator_mem1521
        (isPGroup_of_exp_two1521 hU2) hv2 hZU hUZn hvU hvZ
      have huW : u ∈ W := ⟨huU, hu⟩
      rw [h] at huW
      exact huZ huW
    · exact h
  have hfZ : ∀ x ∈ U, v * x * v⁻¹ * x⁻¹ ∈ Z := fun x hx => by
    have : x ∈ W := hWU' ▸ hx
    exact this.2
  have hUL : U ≤ ⁅U, L⁆ := by
    have hN : L ≤ Subgroup.normalizer ((⁅U, L⁆ : Subgroup G) : Set G) :=
      Subgroup.normalizer_commutator_ge_right U L
    have h3 := commutator_commutator_le_of_rotate1521 (N := ⁅U, L⁆) (H₁ := L) (H₂ := L) (H₃ := Q)
      hN hN (hQL.trans hN)
      (by rw [Subgroup.commutator_comm L Q, hUdef])
      (by rw [hUdef])
    rwa [hLL, Subgroup.commutator_comm L Q, hUdef] at h3
  have hK : ⁅U, L⁆ ≤ U ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine Subgroup.commutator_le.mpr fun u hu l hl => ?_
    have hu' : l * u⁻¹ * l⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hLU hl) _).mp (U.inv_mem hu)
    have hcU : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
    refine Subgroup.mem_inf.mpr ⟨by rw [hcU]; exact U.mul_mem hu hu', ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨z, hzdef⟩ : ∃ z, z = v * u * v⁻¹ * u⁻¹ := ⟨_, rfl⟩
    have hz : z ∈ Z := hzdef ▸ hfZ u hu
    have hzu : v * u * v⁻¹ = z * u := by rw [hzdef]; group
    have hzu' : v * u⁻¹ * v⁻¹ = u⁻¹ * z⁻¹ := by
      have : v * u⁻¹ * v⁻¹ = (v * u * v⁻¹)⁻¹ := by group
      rw [this, hzu]; group
    have h1 := hequiv l hl u⁻¹ (U.inv_mem hu)
    have h3 : l * (u⁻¹ * z⁻¹) * l⁻¹ = (l * u⁻¹ * l⁻¹) * z⁻¹ := by
      have := hZcent _ (Z.inv_mem hz) l hl
      calc l * (u⁻¹ * z⁻¹) * l⁻¹ = (l * u⁻¹ * l⁻¹) * (l * z⁻¹ * l⁻¹) := by group
        _ = (l * u⁻¹ * l⁻¹) * z⁻¹ := by rw [this]
    have hc : v * (u * (l * u⁻¹ * l⁻¹)) * v⁻¹ = u * (l * u⁻¹ * l⁻¹) := by
      calc v * (u * (l * u⁻¹ * l⁻¹)) * v⁻¹
          = (v * u * v⁻¹) * (v * (l * u⁻¹ * l⁻¹) * v⁻¹) := by group
        _ = (z * u) * ((l * u⁻¹ * l⁻¹) * z⁻¹) := by rw [hzu, h1, hzu', h3]
        _ = z * (u * (l * u⁻¹ * l⁻¹)) * z⁻¹ := by group
        _ = u * (l * u⁻¹ * l⁻¹) := by
          rw [hUcomm z (hZU' hz) _ (U.mul_mem hu hu')]; group
    rw [hcU]
    calc u * (l * u⁻¹ * l⁻¹) * v = (v * (u * (l * u⁻¹ * l⁻¹)) * v⁻¹) * v := by rw [hc]
      _ = v * (u * (l * u⁻¹ * l⁻¹)) := by group
  have hcentU : ∀ u ∈ U, v * u = u * v := fun u hu =>
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hK (hUL hu))).2).symm
  have hC : ∀ q ∈ Q, ⁅q, v⁆ ∈ Z := by
    intro q hq
    have hqL : q ∈ L := hQL hq
    have hyU : ⁅q, v⁆ ∈ U := hAU q hqL
    rw [hZmem]
    refine ⟨hyU, fun l hl => ?_⟩
    have hq' : l * q * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hl) q).mp hq
    have hu₁ : ⁅l, v⁆ ∈ U := hAU l hl
    have hw : q⁻¹ * (l * q * l⁻¹) ∈ U := by
      rw [← hUdef]
      have := Subgroup.commutator_mem_commutator (Q.inv_mem hq) hl
      simpa [commutatorElement_def, mul_assoc] using this
    have hwv : v * (q⁻¹ * (l * q * l⁻¹)) = (q⁻¹ * (l * q * l⁻¹)) * v := hcentU _ hw
    have hq'L : l * q * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hqL) (L.inv_mem hl)
    have hy' : ⁅l * q * l⁻¹, v⁆ ∈ U := hAU _ hq'L
    have hcomm' : (l * q * l⁻¹) * ⁅l, v⁆ = ⁅l, v⁆ * (l * q * l⁻¹) :=
      (hUc _ hu₁ _ hq').symm
    have hwv' : (q⁻¹ * (l * q * l⁻¹)) * v * (q⁻¹ * (l * q * l⁻¹))⁻¹ = v := by
      rw [← hwv]; group
    have e1 : l * ⁅q, v⁆ * l⁻¹ =
        (l * q * l⁻¹) * (⁅l, v⁆ * v) * (l * q * l⁻¹)⁻¹ * (⁅l, v⁆ * v)⁻¹ := by
      simp only [commutatorElement_def]; group
    have e2 : (l * q * l⁻¹) * (⁅l, v⁆ * v) * (l * q * l⁻¹)⁻¹ * (⁅l, v⁆ * v)⁻¹ =
        ⁅l, v⁆ * ⁅l * q * l⁻¹, v⁆ * (⁅l, v⁆)⁻¹ := by
      calc (l * q * l⁻¹) * (⁅l, v⁆ * v) * (l * q * l⁻¹)⁻¹ * (⁅l, v⁆ * v)⁻¹
          = ((l * q * l⁻¹) * ⁅l, v⁆) * v * (l * q * l⁻¹)⁻¹ * v⁻¹ * (⁅l, v⁆)⁻¹ := by group
        _ = (⁅l, v⁆ * (l * q * l⁻¹)) * v * (l * q * l⁻¹)⁻¹ * v⁻¹ * (⁅l, v⁆)⁻¹ := by rw [hcomm']
        _ = ⁅l, v⁆ * ⁅l * q * l⁻¹, v⁆ * (⁅l, v⁆)⁻¹ := by
          simp only [commutatorElement_def]; group
    have e3 : ⁅l, v⁆ * ⁅l * q * l⁻¹, v⁆ * (⁅l, v⁆)⁻¹ = ⁅l * q * l⁻¹, v⁆ := by
      rw [hUcomm _ hu₁ _ hy']; group
    have e4 : ⁅l * q * l⁻¹, v⁆ = ⁅q, v⁆ := by
      set w := q⁻¹ * (l * q * l⁻¹) with hwdef
      have hq'w : l * q * l⁻¹ = q * w := by rw [hwdef]; group
      calc ⁅l * q * l⁻¹, v⁆ = q * (w * v * w⁻¹) * q⁻¹ * v⁻¹ := by
            rw [hq'w]; simp only [commutatorElement_def]; group
        _ = ⁅q, v⁆ := by rw [hwv']; simp only [commutatorElement_def]
    have e5 : l * ⁅q, v⁆ * l⁻¹ = ⁅q, v⁆ := by rw [e1, e2, e3, e4]
    calc l * ⁅q, v⁆ = (l * ⁅q, v⁆ * l⁻¹) * l := by group
      _ = ⁅q, v⁆ * l := by rw [e5]
  exact ⟨hAU, hcentU, hC⟩

end Ab1

section Ab2

variable {G : Type} [Group G] [Finite G]

theorem exists_twist_of_odd_index1521 {L U Z H : Subgroup G} {v : G}
    (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU2 : ∀ x ∈ U, x ^ 2 = 1)
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hδU : ∀ l ∈ L, ⁅l, v⁆ ∈ U) (hH : ¬ 2 ∣ (H.subgroupOf L).index)
    (hδH : ∀ h ∈ H, ⁅h, v⁆ ∈ Z) :
    ∃ u ∈ U, ∀ l ∈ L, ⁅l, u * v⁆ ∈ Z := by
  classical
  let _inst : CommGroup ↥U :=
    { (inferInstance : Group ↥U) with mul_comm := fun a b => Subtype.ext (hUc a a.2 b b.2) }
  have : Fintype ↥L := Fintype.ofFinite _
  set H' : Subgroup ↥L := H.subgroupOf L with hH'
  have : Fintype (↥L ⧸ H') := Fintype.ofFinite _
  have hcjmem : ∀ (g : ↥L) (u : ↥U), (g : G) * (u : G) * (g : G)⁻¹ ∈ U :=
    fun g u => (Subgroup.mem_normalizer_iff.mp (hLU g.2) u).mp u.2
  let cj : ↥L → ↥U → ↥U := fun g u => ⟨(g : G) * (u : G) * (g : G)⁻¹, hcjmem g u⟩
  have cj_mul : ∀ g u w, cj g (u * w) = cj g u * cj g w := by
    intro g u w
    apply Subtype.ext
    show (g : G) * ((u : G) * (w : G)) * (g : G)⁻¹ = ((g : G) * (u : G) * (g : G)⁻¹) *
      ((g : G) * (w : G) * (g : G)⁻¹)
    group
  have cj_one : ∀ g, cj g 1 = 1 := by
    intro g
    apply Subtype.ext
    show (g : G) * 1 * (g : G)⁻¹ = 1
    group
  let cjHom : ↥L → ↥U →* ↥U := fun g => ⟨⟨cj g, cj_one g⟩, cj_mul g⟩
  let δ : ↥L → ↥U := fun l => ⟨⁅(l : G), v⁆, hδU l l.2⟩
  have hδmul : ∀ x y : ↥L, δ (x * y) = cj x (δ y) * δ x := by
    intro x y
    apply Subtype.ext
    show ⁅((x * y : ↥L) : G), v⁆ = ((x : G) * ⁅(y : G), v⁆ * (x : G)⁻¹) * ⁅(x : G), v⁆
    simp only [commutatorElement_def, Subgroup.coe_mul]
    group
  have hδ2 : ∀ x : ↥L, δ x * δ x = 1 := by
    intro x
    apply Subtype.ext
    have := hU2 _ (δ x).2
    simpa [pow_two] using this
  let rep : ↥L ⧸ H' → ↥L := fun c => Quotient.out c
  have hrep : ∀ c, (QuotientGroup.mk (rep c) : ↥L ⧸ H') = c := fun c => QuotientGroup.out_eq' c
  have hkey : ∀ (g : ↥L) (c : ↥L ⧸ H'), ∃ z : ↥U, (z : G) ∈ Z ∧
      cj g (δ (rep c)) * δ g = z * δ (rep (g • c)) := by
    intro g c
    set x := rep (g • c) with hx
    set y := rep c with hy
    have h1 : (QuotientGroup.mk x : ↥L ⧸ H') = QuotientGroup.mk (g * y) := by
      have e1 : (QuotientGroup.mk x : ↥L ⧸ H') = g • c := hrep (g • c)
      have e2 : g • c = QuotientGroup.mk (g * y) := by
        conv_lhs => rw [← hrep c]
        rfl
      rw [e1, e2]
    obtain ⟨h, hhdef⟩ : ∃ h : ↥L, h = x⁻¹ * (g * y) := ⟨_, rfl⟩
    have hh : h ∈ H' := hhdef ▸ QuotientGroup.eq.1 h1
    have hhG : (h : G) ∈ H := Subgroup.mem_subgroupOf.mp hh
    have hgy : g * y = x * h := by rw [hhdef]; group
    refine ⟨cj x (δ h), ?_, ?_⟩
    · have hz : (δ h : G) ∈ Z := hδH _ hhG
      exact (Subgroup.mem_normalizer_iff.mp (hLZ x.2) _).mp hz
    · rw [← hδmul g y, hgy, hδmul x h]
  have hodd : Odd (Fintype.card (↥L ⧸ H')) := by
    have h1 : Nat.card (↥L ⧸ H') = Fintype.card (↥L ⧸ H') := Nat.card_eq_fintype_card
    have h2 : H'.index = Fintype.card (↥L ⧸ H') := by rw [Subgroup.index, h1]
    rw [← h2]
    exact Nat.odd_iff.mpr (by omega)
  set a : ↥U := ∏ c : ↥L ⧸ H', δ (rep c) with ha
  have hE : ∀ g : ↥L, ∃ p : ↥U, (p : G) ∈ Z ∧ cj g a * δ g = p * a := by
    intro g
    choose z hzZ hz using hkey g
    refine ⟨∏ c, z c, ?_, ?_⟩
    · have : (∏ c, z c) ∈ Z.subgroupOf U := by
        refine Subgroup.prod_mem _ fun c _ => ?_
        exact Subgroup.mem_subgroupOf.mpr (hzZ c)
      exact Subgroup.mem_subgroupOf.mp this
    · have h1 : ∏ c : ↥L ⧸ H', (cj g (δ (rep c)) * δ g) = ∏ c : ↥L ⧸ H', (z c * δ (rep (g • c))) :=
        Finset.prod_congr rfl fun c _ => hz c
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ] at h1
      have h2 : ∏ c : ↥L ⧸ H', cj g (δ (rep c)) = cj g a := by
        rw [ha]; exact (map_prod (cjHom g) (fun c => δ (rep c)) Finset.univ).symm
      have h3 : ∏ c : ↥L ⧸ H', δ (rep (g • c)) = a :=
        Equiv.prod_comp (MulAction.toPerm g) (fun c => δ (rep c))
      have h4 : δ g ^ Fintype.card (↥L ⧸ H') = δ g := by
        obtain ⟨k, hk⟩ := hodd
        rw [hk, pow_succ, pow_mul, pow_two, hδ2, one_pow, one_mul]
      rw [h2, h4, h3] at h1
      exact h1
  refine ⟨((a⁻¹ : ↥U) : G), (a⁻¹ : ↥U).2, fun l hl => ?_⟩
  obtain ⟨p, hpZ, hp⟩ := hE ⟨l, hl⟩
  have hX : cj ⟨l, hl⟩ a = p * a * δ ⟨l, hl⟩ := by
    calc cj ⟨l, hl⟩ a = cj ⟨l, hl⟩ a * δ ⟨l, hl⟩ * δ ⟨l, hl⟩ := by
          rw [mul_assoc, hδ2, mul_one]
      _ = p * a * δ ⟨l, hl⟩ := by rw [hp]
  have hres : cj ⟨l, hl⟩ a⁻¹ * δ ⟨l, hl⟩ * a = p⁻¹ := by
    have hinv : cj ⟨l, hl⟩ a⁻¹ = (cj ⟨l, hl⟩ a)⁻¹ := map_inv (cjHom ⟨l, hl⟩) a
    rw [hinv, hX, mul_inv_rev, mul_inv_rev]
    calc (δ ⟨l, hl⟩)⁻¹ * (a⁻¹ * p⁻¹) * δ ⟨l, hl⟩ * a
        = ((δ ⟨l, hl⟩)⁻¹ * δ ⟨l, hl⟩) * (a⁻¹ * a) * p⁻¹ := by ac_rfl
      _ = p⁻¹ := by simp
  have hval : ⁅l, ((a⁻¹ : ↥U) : G) * v⁆ = ((cj ⟨l, hl⟩ a⁻¹ * δ ⟨l, hl⟩ * a : ↥U) : G) := by
    show _ = (l * ((a⁻¹ : ↥U) : G) * l⁻¹) * ⁅l, v⁆ * (a : G)
    simp only [commutatorElement_def, Subgroup.coe_inv]
    group
  rw [hval, hres]
  exact Z.inv_mem hpZ

end Ab2

section Ab3

variable {G : Type} [Group G]

theorem centralizes_of_commutator_mem_center1521 {L Z : Subgroup G} {w : G} (hLL : ⁅L, L⁆ = L)
    (hZc : Z ≤ Subgroup.centralizer (L : Set G)) (hwZ : w ∈ Subgroup.normalizer (Z : Set G))
    (h : ∀ l ∈ L, ⁅l, w⁆ ∈ Z) : ∀ l ∈ L, w * l = l * w := by
  let Cw : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (Z : Set G) ∧ ∀ l ∈ L, ⁅l, x⁆ ∈ Z}
      one_mem' := ⟨Subgroup.one_mem _, fun l _ => by simp⟩
      mul_mem' := fun {x₁ x₂} h₁ h₂ => ⟨Subgroup.mul_mem _ h₁.1 h₂.1, fun l hl => by
        have e : ⁅l, x₁ * x₂⁆ = ⁅l, x₁⁆ * (x₁ * ⁅l, x₂⁆ * x₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact Z.mul_mem (h₁.2 l hl) ((Subgroup.mem_normalizer_iff.mp h₁.1 _).mp (h₂.2 l hl))⟩
      inv_mem' := fun {x} h => ⟨Subgroup.inv_mem _ h.1, fun l hl => by
        have e : ⁅l, x⁻¹⁆ = x⁻¹ * (⁅l, x⁆)⁻¹ * x := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h.1) _).mp
          (Z.inv_mem (h.2 l hl))
        simpa using h1⟩ }
  have hV : ⁅L, Subgroup.zpowers w⁆ ≤ Z :=
    Subgroup.commutator_le.mpr fun l hl x hx =>
      (Subgroup.zpowers_le.mpr (show w ∈ Cw from ⟨hwZ, h⟩) hx).2 l hl
  have h1 : ⁅⁅L, Subgroup.zpowers w⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hV.trans hZc)
  have h2 : ⁅⁅Subgroup.zpowers w, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Subgroup.zpowers w) L]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L) (H₂ := L)
    (H₃ := Subgroup.zpowers w) h1 h2
  rw [hLL] at h3
  intro l hl
  have h4 : ⁅l, w⁆ ∈ ⁅L, Subgroup.zpowers w⁆ :=
    Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers w)
  rw [h3, Subgroup.mem_bot, commutatorElement_def] at h4
  have h5 : l * w * l⁻¹ = w := mul_inv_eq_one.mp h4
  calc w * l = (l * w * l⁻¹) * l := by rw [h5]
    _ = l * w := by group

end Ab3

end CFSG.Quasithin
