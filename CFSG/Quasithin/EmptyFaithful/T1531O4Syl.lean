module

public import CFSG.Quasithin.EmptyFaithful.T1531O4Line
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.GroupTheory.KleinFourAutomorphism

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.S1417 CFSG.QuasithinUnique

namespace T1531O4

variable {W : Type*} [CommGroup W]

section Count

variable [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
theorem xor_mem_sup (hS : OfourStruct X L₁ L₂ t) {c b : MulAut W} (hc : c ∈ X) (hcN : c ∉ L₁ ⊔ L₂)
    (hb : b ∈ X) : Xor (b * c ∈ L₁ ⊔ L₂) (b ∈ L₁ ⊔ L₂) := by
  have hsq := mul_self_mem_sup hS hc
  by_cases hbN : b ∈ L₁ ⊔ L₂
  · refine Or.inr ⟨hbN, fun hbc => hcN ?_⟩
    have := (L₁ ⊔ L₂).mul_mem (Subgroup.inv_mem _ hbN) hbc
    simpa using this
  · refine Or.inl ⟨?_, hbN⟩
    rcases coset_of_relIndex_two hS.relIndex_sup hb hc hcN with h | h
    · exact absurd h hbN
    · have e : b * c = (b * c⁻¹) * (c * c) := by group
      rw [e]
      exact (L₁ ⊔ L₂).mul_mem h hsq

theorem card_inf_stab (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) : Nat.card ↥(X ⊓ stabSub E) = 12 := by
  set D : Subgroup (MulAut W) := (L₁ ⊔ L₂) ⊓ stabSub E with hD
  have hDX : D ≤ X ⊓ stabSub E := inf_le_inf_right _ hS.le_X_sup
  have hDL₂ : L₂ ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₂, -, hxs⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_stab_L₂ hS hE hx₂ hxs)
  have hsup : L₂ ⊔ D = L₁ ⊔ L₂ := by
    apply le_antisymm
    · exact sup_le le_sup_right inf_le_left
    · refine sup_le (fun a ha => ?_) le_sup_left
      obtain ⟨l₂, hl₂, hst⟩ := exists_L₂_of_L₁ hS hE ha
      have hmem : a * l₂ ∈ D :=
        ⟨(L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hl₂), hst⟩
      have : a = (a * l₂) * l₂⁻¹ := by group
      rw [this]
      exact (L₂ ⊔ D).mul_mem (Subgroup.mem_sup_right hmem)
        ((L₂ ⊔ D).inv_mem (Subgroup.mem_sup_left hl₂))
  have hcardD : Nat.card D = 6 := by
    have h1 := S143.card_sup_mul_card_inf_of_le_normalizer (R := L₂) (U := D)
      (inf_le_left.trans hS.sup_le_normalizer_L₂)
    rw [hsup, hDL₂, Subgroup.card_bot, hS.card_sup, hS.card_L₂] at h1
    omega
  obtain ⟨c, hcX, hcN, hcS⟩ := exists_swap_stab hS hE
  have hrel : D.relIndex (X ⊓ stabSub E) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨c, ⟨hcX, hcS⟩, fun b hb => ?_⟩
    have hx := xor_mem_sup hS hcX hcN hb.1
    have hbc : b * c ∈ stabSub E := (stabSub E).mul_mem hb.2 hcS
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨⟨h1, hbc⟩, fun h => h2 h.1⟩
    · exact Or.inr ⟨⟨h1, hb.2⟩, fun h => h2 h.1⟩
  have h1 := Subgroup.relIndex_mul_card D (X ⊓ stabSub E)
  rw [inf_eq_left.mpr hDX, hrel, hcardD] at h1
  omega

theorem card_eq_four_of_sylow_stab (hS : OfourStruct X L₁ L₂ t) {E : Subgroup W}
    (hE : IsLine (commV L₁) (commV L₂) E) {P : Subgroup (MulAut W)}
    (hP : IsSylowTwoOf P (X ⊓ stabSub E)) : Nat.card P = 4 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP.2.1
  have h1 := Subgroup.relIndex_mul_card P (X ⊓ stabSub E)
  rw [inf_eq_left.mpr hP.1, hk, card_inf_stab hS hE] at h1
  have hodd : ¬ 2 ∣ P.relIndex (X ⊓ stabSub E) := hP.2.2
  rcases k with _ | _ | _ | k
  · exfalso
    apply hodd
    have : P.relIndex (X ⊓ stabSub E) = 12 := by simpa using h1
    rw [this]
    norm_num
  · exfalso
    apply hodd
    have : P.relIndex (X ⊓ stabSub E) = 6 := by
      have : P.relIndex (X ⊓ stabSub E) * 2 = 12 := by simpa using h1
      omega
    rw [this]
    norm_num
  · simpa using hk
  · exfalso
    have : 8 ∣ 12 := ⟨P.relIndex (X ⊓ stabSub E) * 2 ^ k, by rw [← h1]; ring⟩
    omega

end Count

section Fix

variable {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem fixV_one : fixV (Subgroup.zpowers (1 : MulAut W)) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  rw [mem_fixV_zpowers_iff]
  simp

theorem fixV_mul_eq (hS : OfourStruct X L₁ L₂ t) {m₁ m₂ : MulAut W} (hm₁ : m₁ ∈ L₁)
    (hm₂ : m₂ ∈ L₂) :
    fixV (Subgroup.zpowers (m₁ * m₂)) =
      (commV L₁ ⊓ fixV (Subgroup.zpowers m₁)) ⊔ (commV L₂ ⊓ fixV (Subgroup.zpowers m₂)) := by
  apply le_antisymm
  · intro w hw
    rw [mem_fixV_zpowers_iff] at hw
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hS.exists_decomp_W w
    obtain ⟨h1, h2⟩ := hS.fix_of_fix_mul hm₁ hm₂ hw
    have e1 : m₁ (u₁ * u₂) = m₁ u₁ * u₂ := by rw [map_mul, hS.L₁_fix₂ hm₁ hu₂]
    have e2 : m₂ (u₁ * u₂) = u₁ * m₂ u₂ := by rw [map_mul, hS.L₂_fix₁ hm₂ hu₁]
    have hu₁f : m₁ u₁ = u₁ := by
      rw [e1] at h1
      exact mul_right_cancel h1
    have hu₂f : m₂ u₂ = u₂ := by
      rw [e2] at h2
      exact mul_left_cancel h2
    exact Subgroup.mul_mem_sup ⟨hu₁, mem_fixV_zpowers_iff.mpr hu₁f⟩
      ⟨hu₂, mem_fixV_zpowers_iff.mpr hu₂f⟩
  · refine sup_le ?_ ?_
    · intro u hu'
      obtain ⟨hu, hf⟩ := Subgroup.mem_inf.mp hu'
      rw [mem_fixV_zpowers_iff] at hf ⊢
      rw [MulAut.mul_apply, hS.L₂_fix₁ hm₂ hu, hf]
    · intro u hu'
      obtain ⟨hu, hf⟩ := Subgroup.mem_inf.mp hu'
      rw [mem_fixV_zpowers_iff] at hf ⊢
      rw [MulAut.mul_apply, hf, hS.L₁_fix₂ hm₁ hu]

theorem inf_fixV_eq_zpowers {U : Subgroup W} {s : MulAut W} {a : W} (haU : a ∈ U)
    (hfix : ∀ u ∈ U, s u = u ↔ (u = 1 ∨ u = a)) :
    U ⊓ fixV (Subgroup.zpowers s) = Subgroup.zpowers a := by
  refine Subgroup.ext fun u => ?_
  constructor
  · intro h
    obtain ⟨hu, hf⟩ := Subgroup.mem_inf.mp h
    have hf' : s u = u := mem_fixV_zpowers_iff.mp hf
    rcases (hfix u hu).mp hf' with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · intro hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine Subgroup.mem_inf.mpr ⟨U.zpow_mem haU k, mem_fixV_zpowers_iff.mpr ?_⟩
    rw [map_zpow, (hfix a haU).mpr (Or.inr rfl)]

theorem card_zpowers_of_sq {α : Type*} [Group α] {a : α} (ha1 : a ≠ 1) (ha : a ^ 2 = 1) :
    Nat.card (Subgroup.zpowers a) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers, orderOf_eq_prime ha ha1]

theorem rk_eq_of_card [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) {H : Subgroup W} {n : ℕ}
    (h : Nat.card H = 2 ^ n) : rk H = n := by
  have := card_eq_two_pow hexp H
  rw [h] at this
  exact (Nat.pow_right_injective le_rfl this).symm

theorem rk_fixV_mul [Finite W] (hS : OfourStruct X L₁ L₂ t) {m₁ m₂ : MulAut W} (hm₁ : m₁ ∈ L₁)
    (hm₂ : m₂ ∈ L₂) :
    rk (fixV (Subgroup.zpowers (m₁ * m₂))) =
      rk ↥(commV L₁ ⊓ fixV (Subgroup.zpowers m₁)) + rk ↥(commV L₂ ⊓ fixV (Subgroup.zpowers m₂)) := by
  rw [fixV_mul_eq hS hm₁ hm₂]
  have hinf : (commV L₁ ⊓ fixV (Subgroup.zpowers m₁)) ⊓ (commV L₂ ⊓ fixV (Subgroup.zpowers m₂)) =
      ⊥ := by
    refine eq_bot_iff.mpr fun w hw => ?_
    have : w ∈ commV L₁ ⊓ commV L₂ := ⟨hw.1.1, hw.2.1⟩
    rw [hS.inf] at this
    exact this
  have := rk_sup_add_rk_inf (commV L₁ ⊓ fixV (Subgroup.zpowers m₁))
    (commV L₂ ⊓ fixV (Subgroup.zpowers m₂))
  rw [hinf, rk_bot] at this
  omega

theorem rk_U₁ [Finite W] (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1) :
    rk (commV L₁) = 2 := rk_eq_of_card hexp (by rw [hS.card_U₁]; norm_num)

theorem rk_U₂ [Finite W] (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1) :
    rk (commV L₂) = 2 :=
  rk_eq_of_card hexp (by rw [(card_of_actsAsNaturalL2 hS.nat₂).2]; norm_num)

theorem rk_W [Finite W] (hS : OfourStruct X L₁ L₂ t) : rk W = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [card_W hS]
  have : (16 : ℕ) = 2 ^ 4 := by norm_num
  rw [this, padicValNat.prime_pow]

theorem rk_fix_S [Finite W] (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    {S : Subgroup (MulAut W)} {s₁ s₂ : MulAut W} {a₁ a₂ : W}
    (hd : CFSG.Quasithin.S1417.SylowData S L₁ L₂ s₁ s₂ a₁ a₂) :
    rk (fixV (Subgroup.zpowers s₁)) = 3 ∧ rk (fixV (Subgroup.zpowers s₂)) = 3 ∧
      rk (fixV (Subgroup.zpowers (s₁ * s₂))) = 2 ∧
      rk (fixV (Subgroup.zpowers (1 : MulAut W))) = 4 := by
  have h1 : commV L₁ ⊓ fixV (Subgroup.zpowers s₁) = Subgroup.zpowers a₁ :=
    inf_fixV_eq_zpowers hd.a₁_mem hd.fix₁
  have h2 : commV L₂ ⊓ fixV (Subgroup.zpowers s₂) = Subgroup.zpowers a₂ :=
    inf_fixV_eq_zpowers hd.a₂_mem hd.fix₂
  have ha₁sq : a₁ ^ 2 = 1 := hexp a₁
  have ha₂sq : a₂ ^ 2 = 1 := hexp a₂
  have rk₁ : rk ↥(Subgroup.zpowers a₁) = 1 :=
    rk_eq_of_card hexp (by rw [card_zpowers_of_sq hd.a₁_ne ha₁sq]; norm_num)
  have rk₂ : rk ↥(Subgroup.zpowers a₂) = 1 :=
    rk_eq_of_card hexp (by rw [card_zpowers_of_sq hd.a₂_ne ha₂sq]; norm_num)
  have hone₁ : commV L₁ ⊓ fixV (Subgroup.zpowers (1 : MulAut W)) = commV L₁ := by
    rw [fixV_one, inf_top_eq]
  have hone₂ : commV L₂ ⊓ fixV (Subgroup.zpowers (1 : MulAut W)) = commV L₂ := by
    rw [fixV_one, inf_top_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := rk_fixV_mul hS hd.s₁_mem_L (Subgroup.one_mem L₂)
    rw [mul_one, h1, hone₂, rk₁, rk_U₂ hS hexp] at this
    exact this
  · have := rk_fixV_mul hS (Subgroup.one_mem L₁) hd.s₂_mem_L
    rw [one_mul, h2, hone₁, rk₂, rk_U₁ hS hexp] at this
    exact this
  · have := rk_fixV_mul hS hd.s₁_mem_L hd.s₂_mem_L
    rw [h1, h2, rk₁, rk₂] at this
    exact this
  · rw [fixV_one, rk_top, rk_W hS]

theorem swap_apply_mem' (hS : OfourStruct X L₁ L₂ t) {x : MulAut W} (hX : x ∈ X)
    (hxN : x ∉ L₁ ⊔ L₂) :
    (∀ u ∈ commV L₁, x u ∈ commV L₂) ∧ (∀ u ∈ commV L₂, x u ∈ commV L₁) := by
  have hxt : x * t ∈ L₁ ⊔ L₂ := (hS.mem_or_mul_t_mem hX).resolve_left hxN
  have htt : ∀ u : W, t (t u) = u := fun u => by
    have := congrArg (fun φ : MulAut W => φ u) hS.tsq
    simpa using this
  have hx_eq : ∀ u : W, x u = (x * t) (t u) := fun u => by rw [MulAut.mul_apply, htt]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rw [hx_eq]
    exact (mem_stabSub.1 (hS.sup_le_stab₂ hxt) (t u)).2 (hS.swap₁ u hu)
  · rw [hx_eq]
    exact (mem_stabSub.1 (hS.sup_le_stab₁ hxt) (t u)).2 (hS.swap₂ u hu)

theorem rk_fixV_swap [Finite W] (hS : OfourStruct X L₁ L₂ t) {g : MulAut W} (hX : g ∈ X)
    (hN : g ∉ L₁ ⊔ L₂) :
    rk (fixV (Subgroup.zpowers g)) = rk ↥(commV L₁ ⊓ fixV (Subgroup.zpowers (g * g))) := by
  obtain ⟨hs₁, hs₂⟩ := swap_apply_mem' hS hX hN
  have hcard : Nat.card ↥(commV L₁ ⊓ fixV (Subgroup.zpowers (g * g))) =
      Nat.card ↥(fixV (Subgroup.zpowers g)) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun u : ↥(commV L₁ ⊓ fixV (Subgroup.zpowers (g * g))) =>
        (⟨u.1 * g u.1, ?_⟩ : ↥(fixV (Subgroup.zpowers g)))) ⟨?_, ?_⟩)
    · have hgg : g (g u.1) = u.1 := mem_fixV_zpowers_iff.mp u.2.2
      rw [mem_fixV_zpowers_iff, map_mul, hgg, mul_comm]
    · intro u u' h
      have h' : u.1 * g u.1 = u'.1 * g u'.1 := congrArg Subtype.val h
      exact Subtype.ext (eq_of_mul_eq_of_inf_eq_bot hS.inf u.2.1 u'.2.1 (hs₁ _ u.2.1)
        (hs₁ _ u'.2.1) h').1
    · rintro ⟨w, hw⟩
      have hgw : g w = w := mem_fixV_zpowers_iff.mp hw
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hS.exists_decomp_W w
      have hgw' : g u₂ * g u₁ = u₁ * u₂ := by
        rw [← hgw, map_mul, mul_comm]
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_inf_eq_bot hS.inf (hs₂ _ hu₂) hu₁ (hs₁ _ hu₁) hu₂ hgw'
      have hmem : u₁ ∈ commV L₁ ⊓ fixV (Subgroup.zpowers (g * g)) := by
        refine ⟨hu₁, mem_fixV_zpowers_iff.mpr ?_⟩
        rw [MulAut.mul_apply, h2, h1]
      refine ⟨⟨u₁, hmem⟩, Subtype.ext ?_⟩
      show u₁ * g u₁ = u₁ * u₂
      rw [h2]
  unfold rk
  rw [hcard]

theorem rk_fixV_swap_one [Finite W] (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    {g : MulAut W} (hX : g ∈ X) (hN : g ∉ L₁ ⊔ L₂) (hg : g * g = 1) :
    rk (fixV (Subgroup.zpowers g)) = 2 := by
  rw [rk_fixV_swap hS hX hN, hg, fixV_one, inf_top_eq, rk_U₁ hS hexp]

theorem rk_fixV_swap_s [Finite W] (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    {S : Subgroup (MulAut W)} {s₁ s₂ : MulAut W} {a₁ a₂ : W}
    (hd : CFSG.Quasithin.S1417.SylowData S L₁ L₂ s₁ s₂ a₁ a₂)
    {g : MulAut W} (hX : g ∈ X) (hN : g ∉ L₁ ⊔ L₂) (hg : g * g = s₁ * s₂) :
    rk (fixV (Subgroup.zpowers g)) = 1 := by
  rw [rk_fixV_swap hS hX hN, hg]
  have h1 : commV L₁ ⊓ fixV (Subgroup.zpowers (s₁ * s₂)) =
      commV L₁ ⊓ fixV (Subgroup.zpowers s₁) := by
    refine Subgroup.ext fun u => ?_
    constructor
    · rintro ⟨hu, hf⟩
      refine ⟨hu, mem_fixV_zpowers_iff.mpr ?_⟩
      have := mem_fixV_zpowers_iff.mp hf
      rwa [MulAut.mul_apply, hS.L₂_fix₁ hd.s₂_mem_L hu] at this
    · rintro ⟨hu, hf⟩
      refine ⟨hu, mem_fixV_zpowers_iff.mpr ?_⟩
      have := mem_fixV_zpowers_iff.mp hf
      rwa [MulAut.mul_apply, hS.L₂_fix₁ hd.s₂_mem_L hu]
  rw [h1, inf_fixV_eq_zpowers hd.a₁_mem hd.fix₁]
  exact rk_eq_of_card hexp (by rw [card_zpowers_of_sq hd.a₁_ne (hexp a₁)]; norm_num)

end Fix

section SylowLine

variable [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W} {T' : Subgroup (MulAut W)}
  {s₁ s₂ τ : MulAut W} {a₁ a₂ : W}

omit [Finite W] in
theorem S_comm_gens (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂)
    {x : MulAut W} (hx : x ∈ T' ⊓ (L₁ ⊔ L₂)) : x * s₁ = s₁ * x ∧ x * s₂ = s₂ * x := by
  have c12 : Commute s₁ s₂ := hF.comm
  rcases (hF.S_eq x).1 hx with rfl | rfl | rfl | rfl
  · simp
  · exact ⟨rfl, c12.eq⟩
  · exact ⟨c12.symm.eq, rfl⟩
  · exact ⟨((Commute.refl s₁).mul_left c12.symm).eq, (c12.mul_left (Commute.refl s₂)).eq⟩

theorem conj_swap (hS : OfourStruct X L₁ L₂ t) (hT : IsSylowTwoOf T' X)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {g : MulAut W} (hg : g ∈ T')
    (hgN : g ∉ L₁ ⊔ L₂) : g * s₁ * g⁻¹ = s₂ ∧ g * s₂ * g⁻¹ = s₁ := by
  have hτS : τ ∉ T' ⊓ (L₁ ⊔ L₂) := fun h => hF.τ_N h.2
  have hgS : g ∉ T' ⊓ (L₁ ⊔ L₂) := fun h => hgN h.2
  rcases coset_of_relIndex_two (hS.relIndex_S hT) hg hF.τ_T hτS with h | h
  · exact absurd h hgS
  · obtain ⟨x, hxdef⟩ : ∃ x, x = g * τ⁻¹ := ⟨_, rfl⟩
    rw [← hxdef] at h
    have hg' : g = x * τ := by rw [hxdef]; group
    obtain ⟨hx1, hx2⟩ := S_comm_gens hF h
    refine ⟨?_, ?_⟩
    · calc g * s₁ * g⁻¹ = x * (τ * s₁ * τ⁻¹) * x⁻¹ := by rw [hg']; group
        _ = x * s₂ * x⁻¹ := by rw [hF.τs₁]
        _ = s₂ := by rw [hx2]; group
    · calc g * s₂ * g⁻¹ = x * (τ * s₂ * τ⁻¹) * x⁻¹ := by rw [hg']; group
        _ = x * s₁ * x⁻¹ := by rw [hF.τs₂]
        _ = s₁ := by rw [hx1]; group

theorem sq_mem_S (hS : OfourStruct X L₁ L₂ t) (hT : IsSylowTwoOf T' X) {g : MulAut W}
    (hg : g ∈ T') : g * g ∈ T' ⊓ (L₁ ⊔ L₂) := by
  by_cases hgS : g ∈ T' ⊓ (L₁ ⊔ L₂)
  · exact Subgroup.mul_mem _ hgS hgS
  · rcases coset_of_relIndex_two (hS.relIndex_S hT) (T'.mul_mem hg hg) hg hgS with h | h
    · exact h
    · have : g * g * g⁻¹ = g := by group
      rw [this] at h
      exact absurd h hgS

theorem sq_of_swap (hS : OfourStruct X L₁ L₂ t) (hT : IsSylowTwoOf T' X)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {g : MulAut W} (hg : g ∈ T')
    (hgN : g ∉ L₁ ⊔ L₂) : g * g = 1 ∨ g * g = s₁ * s₂ := by
  have hsq := sq_mem_S hS hT hg
  obtain ⟨h1, h2⟩ := conj_swap hS hT hF hg hgN
  have hconj : g * (g * g) * g⁻¹ = g * g := by group
  rcases (hF.S_eq _).1 hsq with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h, h1] at hconj
    exact hF.ne hconj.symm
  · exfalso
    rw [h, h2] at hconj
    exact hF.ne hconj
  · exact Or.inr h

omit [Finite W] in
theorem ss_sq (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) : (s₁ * s₂) * (s₁ * s₂) = 1 := by
  calc (s₁ * s₂) * (s₁ * s₂) = s₁ * (s₂ * s₁) * s₂ := by group
    _ = s₁ * (s₁ * s₂) * s₂ := by rw [← hF.comm]
    _ = (s₁ * s₁) * (s₂ * s₂) := by group
    _ = 1 := by rw [hF.s₁_sq, hF.s₂_sq, one_mul]

omit [Finite W] in
theorem isKleinFour_of_isLine (hexp : ∀ w : W, w ^ 2 = 1) {U₁ U₂ E : Subgroup W}
    (hE : IsLine U₁ U₂ E) : IsKleinFour ↥E := by
  have hsq : ∀ x : ↥E, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hexp x.1)
  have hexp' : Monoid.exponent ↥E = 2 := by
    have hdvd : Monoid.exponent ↥E ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hsub : Subsingleton ↥E := Monoid.exp_eq_one_iff.mp h1
      have := Nat.card_of_subsingleton (1 : ↥E)
      rw [hE.card_eq] at this
      omega
    · exact h2
  exact ⟨hE.card_eq, hexp'⟩

variable {E : Subgroup W}

theorem s_not_mem_stab (hS : OfourStruct X L₁ L₂ t) (hE : IsLine (commV L₁) (commV L₂) E)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) :
    s₁ ∉ stabSub E ∧ s₂ ∉ stabSub E :=
  ⟨fun h => hF.sylow.s₁_ne (eq_one_of_mem_stab_L₁ hS hE hF.sylow.s₁_mem_L h),
    fun h => hF.sylow.s₂_ne (eq_one_of_mem_stab_L₂ hS hE hF.sylow.s₂_mem_L h)⟩

theorem inf_stab_eq (hS : OfourStruct X L₁ L₂ t) (hE : IsLine (commV L₁) (commV L₂) E)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {x : MulAut W}
    (hx : x ∈ T' ⊓ (L₁ ⊔ L₂)) (hxs : x ∈ stabSub E) : x = 1 ∨ x = s₁ * s₂ := by
  obtain ⟨hs₁, hs₂⟩ := s_not_mem_stab hS hE hF
  rcases (hF.S_eq x).1 hx with h | h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hxs) hs₁
  · exact absurd (h ▸ hxs) hs₂
  · exact Or.inr h

theorem s₁s₂_mem_stab (hS : OfourStruct X L₁ L₂ t) (hT : IsSylowTwoOf T' X)
    (hE : IsLine (commV L₁) (commV L₂) E)
    (hTE : IsSylowTwoOf (T' ⊓ stabSub E) (X ⊓ stabSub E))
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) : s₁ * s₂ ∈ stabSub E := by
  have hcard : Nat.card ↥(T' ⊓ stabSub E) = 4 := card_eq_four_of_sylow_stab hS hE hTE
  have hidx : (T' ⊓ (L₁ ⊔ L₂)).relIndex (T' ⊓ stabSub E) ≤ 2 := by
    have h1 := Subgroup.relIndex_le_of_le_right (H := T' ⊓ (L₁ ⊔ L₂)) (K := T' ⊓ stabSub E)
      (L := T') inf_le_left (by rw [hS.relIndex_S hT]; norm_num)
    rwa [hS.relIndex_S hT] at h1
  have hmul := Subgroup.relIndex_mul_card (T' ⊓ (L₁ ⊔ L₂)) (T' ⊓ stabSub E)
  rw [hcard] at hmul
  have hpos : 0 < Nat.card ↥((T' ⊓ (L₁ ⊔ L₂)) ⊓ (T' ⊓ stabSub E)) := Nat.card_pos
  have hK2 : 2 ≤ Nat.card ↥((T' ⊓ (L₁ ⊔ L₂)) ⊓ (T' ⊓ stabSub E)) := by
    by_contra hlt
    push Not at hlt
    nlinarith
  obtain ⟨x, hxK, hx1⟩ : ∃ x ∈ (T' ⊓ (L₁ ⊔ L₂)) ⊓ (T' ⊓ stabSub E), x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (T' ⊓ (L₁ ⊔ L₂)) ⊓ (T' ⊓ stabSub E) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [this, Subgroup.card_bot] at hK2
    omega
  have := (inf_stab_eq hS hE hF hxK.1 hxK.2.2).resolve_left hx1
  rw [← this]
  exact hxK.2.2

omit [Finite W] in
theorem partner_s (hS : OfourStruct X L₁ L₂ t) (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂)
    (hmul : s₁ * s₂ ∈ stabSub E) {x y : W} (hx : x ∈ commV L₁) (hy : y ∈ commV L₂)
    (h : x * y ∈ E) : s₁ x * s₂ y ∈ E :=
  ((mem_stab_mul_iff hS hF.sylow.s₁_mem_L hF.sylow.s₂_mem_L).1 hmul x hx y hy).2 h

theorem a_mul_mem (hS : OfourStruct X L₁ L₂ t) (hE : IsLine (commV L₁) (commV L₂) E)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) (hmul : s₁ * s₂ ∈ stabSub E) :
    a₁ * a₂ ∈ E := by
  have hd := hF.sylow
  obtain ⟨y, hy, hay⟩ := exists_partner₂ hS hE a₁
  have h1 := partner_s hS hF hmul hd.a₁_mem hy hay
  have hs₁a : s₁ a₁ = a₁ := (hd.fix₁ a₁ hd.a₁_mem).mpr (Or.inr rfl)
  rw [hs₁a] at h1
  have hs₂y : s₂ y = y := partner_unique hE (commV_stable L₂ hd.s₂_mem_L hy) hy h1 hay
  rcases (hd.fix₂ y hy).mp hs₂y with rfl | rfl
  · exfalso
    have : a₁ ∈ E ⊓ commV L₁ := ⟨by simpa using hay, hd.a₁_mem⟩
    rw [hE.inf₁, Subgroup.mem_bot] at this
    exact hd.a₁_ne this
  · exact hay

theorem exists_move (hS : OfourStruct X L₁ L₂ t) (hE : IsLine (commV L₁) (commV L₂) E)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) : ∃ e ∈ E, (s₁ * s₂) e ≠ e := by
  have hd := hF.sylow
  obtain ⟨x, hx, hxne⟩ : ∃ x ∈ commV L₁, s₁ x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hd.s₁_ne (eq_one_of_forall_apply_eq hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu)
      hd.s₁_mem_L hcon)
  obtain ⟨y, hy, hxy⟩ := exists_partner₂ hS hE x
  refine ⟨x * y, hxy, fun h => hxne ?_⟩
  rw [mul_apply_prod hS hd.s₁_mem_L hd.s₂_mem_L hx hy] at h
  exact (eq_of_mul_eq_of_inf_eq_bot hS.inf (commV_stable L₁ hd.s₁_mem_L hx) hx
    (commV_stable L₂ hd.s₂_mem_L hy) hy h).1

theorem sq_eq_one_of_mem (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    (hT : IsSylowTwoOf T' X) (hE : IsLine (commV L₁) (commV L₂) E)
    (hTE : IsSylowTwoOf (T' ⊓ stabSub E) (X ⊓ stabSub E))
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {g : MulAut W}
    (hg : g ∈ T' ⊓ stabSub E) : g * g = 1 := by
  have hmul := s₁s₂_mem_stab hS hT hE hTE hF
  by_cases hgN : g ∈ L₁ ⊔ L₂
  · rcases inf_stab_eq hS hE hF ⟨hg.1, hgN⟩ hg.2 with h | h
    · rw [h, mul_one]
    · rw [h]
      exact ss_sq hF
  · rcases sq_of_swap hS hT hF hg.1 hgN with h | h
    · exact h
    · exfalso
      have hKE : IsKleinFour ↥E := isKleinFour_of_isLine hexp hE
      let ρ : ↥(stabSub E) →* MulAut ↥E := resHom E
      let g' : ↥(stabSub E) := ⟨g, hg.2⟩
      let z : ↥(stabSub E) := ⟨s₁ * s₂, hmul⟩
      have hg'z : g' * g' = z := Subtype.ext h
      have hzz : z * z = 1 := Subtype.ext (ss_sq hF)
      have hρz : ρ z ≠ 1 := by
        intro h1
        obtain ⟨e, he, hne⟩ := exists_move hS hE hF
        apply hne
        have h3 : ((ρ z ⟨e, he⟩ : ↥E) : W) = (s₁ * s₂) e := rfl
        rw [h1] at h3
        simpa using h3.symm
      have h2 : ρ g' ^ 2 = ρ z := by rw [pow_two, ← map_mul, hg'z]
      have h4 : ρ g' ^ 4 = 1 := by
        have : ρ g' ^ 4 = (ρ g' ^ 2) ^ 2 := by rw [← pow_mul]
        rw [this, h2, pow_two, ← map_mul, hzz, map_one]
      have hord : orderOf (ρ g') = 4 := by
        have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ρ g')
          (by rw [pow_one, h2]; exact hρz) (by simpa using h4)
        simpa using this
      have hdvd := orderOf_dvd_natCard (ρ g')
      rw [CFSG.kleinFour_automorphism_card, hord] at hdvd
      omega

theorem exists_swap_mem_TE (hS : OfourStruct X L₁ L₂ t) (hE : IsLine (commV L₁) (commV L₂) E)
    (hTE : IsSylowTwoOf (T' ⊓ stabSub E) (X ⊓ stabSub E))
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) :
    ∃ τ' ∈ T' ⊓ stabSub E, τ' ∉ L₁ ⊔ L₂ := by
  by_contra hcon
  push Not at hcon
  have hcard : Nat.card ↥(T' ⊓ stabSub E) = 4 := card_eq_four_of_sylow_stab hS hE hTE
  have hle : T' ⊓ stabSub E ≤ Subgroup.zpowers (s₁ * s₂) := by
    intro x hx
    rcases inf_stab_eq hS hE hF ⟨hx.1, hcon x hx⟩ hx.2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have h1 := Subgroup.card_le_of_le hle
  rw [card_zpowers_of_sq hF.mul_ne (by rw [pow_two]; exact ss_sq hF)] at h1
  omega

theorem mem_stab_of_sq_one (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    (hT : IsSylowTwoOf T' X) (hE : IsLine (commV L₁) (commV L₂) E)
    (hTE : IsSylowTwoOf (T' ⊓ stabSub E) (X ⊓ stabSub E))
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {g : MulAut W} (hg : g ∈ T')
    (hgN : g ∉ L₁ ⊔ L₂) (hg2 : g * g = 1) : g ∈ stabSub E := by
  have hmul := s₁s₂_mem_stab hS hT hE hTE hF
  obtain ⟨τ', hτ'TE, hτ'N⟩ := exists_swap_mem_TE hS hE hTE hF
  have hτ'2 : τ' * τ' = 1 := sq_eq_one_of_mem hS hexp hT hE hTE hF hτ'TE
  have hτ'S : τ' ∉ T' ⊓ (L₁ ⊔ L₂) := fun h => hτ'N h.2
  have hgS : g ∉ T' ⊓ (L₁ ⊔ L₂) := fun h => hgN h.2
  rcases coset_of_relIndex_two (hS.relIndex_S hT) hg hτ'TE.1 hτ'S with h | h
  · exact absurd h hgS
  · obtain ⟨s', hs'def⟩ : ∃ s', s' = g * τ'⁻¹ := ⟨_, rfl⟩
    rw [← hs'def] at h
    have hg' : g = s' * τ' := by rw [hs'def]; group
    obtain ⟨c1, c2⟩ := conj_swap hS hT hF hτ'TE.1 hτ'N
    have key : s' * (τ' * s' * τ'⁻¹) = 1 := by
      have h5 : g * g = s' * (τ' * s' * τ'⁻¹) * (τ' * τ') := by rw [hg']; group
      rw [hτ'2, mul_one, hg2] at h5
      exact h5.symm
    rcases (hF.S_eq s').1 h with hs | hs | hs | hs
    · rw [hg', hs, one_mul]
      exact hτ'TE.2
    · rw [hs, c1] at key
      exact absurd key hF.mul_ne
    · rw [hs, c2] at key
      exact absurd (hF.comm.trans key) hF.mul_ne
    · rw [hg', hs]
      exact (stabSub E).mul_mem hmul hτ'TE.2

theorem even_comm_iff (hS : OfourStruct X L₁ L₂ t) (g : MulAut W) :
    Even (rk (commV (Subgroup.zpowers g))) ↔ Even (rk (fixV (Subgroup.zpowers g))) := by
  have h := rk_commV_add_rk_fixV g
  rw [rk_W hS] at h
  rw [Nat.even_iff, Nat.even_iff]
  omega

theorem dickson_char (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    (hT : IsSylowTwoOf T' X) (hE : IsLine (commV L₁) (commV L₂) E)
    (hTE : IsSylowTwoOf (T' ⊓ stabSub E) (X ⊓ stabSub E))
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {g : MulAut W} (hg : g ∈ T') :
    g ∈ stabSub E ↔ Even (rk (commV (Subgroup.zpowers g))) := by
  have hmul := s₁s₂_mem_stab hS hT hE hTE hF
  obtain ⟨hs₁, hs₂⟩ := s_not_mem_stab hS hE hF
  obtain ⟨rk1, rk2, rk12, rk0⟩ := rk_fix_S hS hexp hF.sylow
  rw [even_comm_iff hS]
  by_cases hgN : g ∈ L₁ ⊔ L₂
  · rcases (hF.S_eq g).1 ⟨hg, hgN⟩ with rfl | rfl | rfl | rfl
    · rw [rk0]
      exact iff_of_true (stabSub E).one_mem (by decide)
    · rw [rk1]
      exact iff_of_false hs₁ (by decide)
    · rw [rk2]
      exact iff_of_false hs₂ (by decide)
    · rw [rk12]
      exact iff_of_true hmul (by decide)
  · have hX : g ∈ X := hT.1 hg
    rcases sq_of_swap hS hT hF hg hgN with h | h
    · rw [rk_fixV_swap_one hS hexp hX hgN h]
      exact iff_of_true (mem_stab_of_sq_one hS hexp hT hE hTE hF hg hgN h) (by decide)
    · rw [rk_fixV_swap_s hS hexp hF.sylow hX hgN h]
      refine iff_of_false (fun hgs => ?_) (by decide)
      have := sq_eq_one_of_mem hS hexp hT hE hTE hF ⟨hg, hgs⟩
      rw [h] at this
      exact hF.mul_ne this

theorem sylow_line (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    (hT : IsSylowTwoOf T' X) (hE : IsLine (commV L₁) (commV L₂) E)
    (hTE : IsSylowTwoOf (T' ⊓ stabSub E) (X ⊓ stabSub E))
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) :
    Nat.card ↥(T' ⊓ stabSub E) = 4 ∧
    (∀ g ∈ T' ⊓ stabSub E, g * g = 1) ∧
    (∀ g ∈ T' ⊓ stabSub E, ∀ h ∈ T' ⊓ stabSub E, g * h = h * g) ∧
    T' ⊓ stabSub E ≠ T' ⊓ (L₁ ⊔ L₂) ∧
    (∀ g ∈ T', g ∈ stabSub E ↔ Even (rk (commV (Subgroup.zpowers g)))) ∧
    (∀ w : W, (∀ x ∈ T', x w = w) → w ∈ E) ∧
    (∃ g ∈ T' ⊓ stabSub E, ∃ e ∈ E, g e ≠ e) := by
  have hmul := s₁s₂_mem_stab hS hT hE hTE hF
  have hsq : ∀ g ∈ T' ⊓ stabSub E, g * g = 1 := fun g hg =>
    sq_eq_one_of_mem hS hexp hT hE hTE hF hg
  refine ⟨card_eq_four_of_sylow_stab hS hE hTE, hsq, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    have h1 : g * h * (g * h) = 1 := hsq _ ((T' ⊓ stabSub E).mul_mem hg hh)
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hsq g hg)
    have hhi : h⁻¹ = h := inv_eq_of_mul_eq_one_right (hsq h hh)
    have h2 : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right h1
    rw [mul_inv_rev, hgi, hhi] at h2
    exact h2.symm
  · intro heq
    obtain ⟨hs₁, -⟩ := s_not_mem_stab hS hE hF
    have : s₁ ∈ T' ⊓ (L₁ ⊔ L₂) := hF.sylow.s₁_mem_S
    rw [← heq] at this
    exact hs₁ this.2
  · intro g hg
    exact dickson_char hS hexp hT hE hTE hF hg
  · intro w hw
    rcases hF.fix w hw with rfl | rfl
    · exact E.one_mem
    · exact a_mul_mem hS hE hF hmul
  · exact ⟨s₁ * s₂, ⟨T'.mul_mem hF.sylow.s₁_mem_S.1 hF.sylow.s₂_mem_S.1, hmul⟩,
      exists_move hS hE hF⟩

end SylowLine

end T1531O4

end CFSG.Quasithin
