module

public import CFSG.Quasithin.Background.B1More13B
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Star
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

section Generic

variable {V : Type} [CommGroup V] [Finite V]

theorem rk_map_mk (A C : Subgroup V) :
    rk ↥(A.map (QuotientGroup.mk' C)) + rk ↥(A ⊓ C) = rk ↥A := by
  have h := CFSG.Quasithin.B1More.card_map_mul_card_inf_ker A (QuotientGroup.mk' C)
  rw [QuotientGroup.ker_mk'] at h
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h]

theorem secIsoOn_rk {X : Subgroup (MulAut V)} {A A₀ B B₀ : Subgroup V}
    (h : SecIsoOn X A A₀ B B₀) : rk ↥A + rk ↥B₀ = rk ↥B + rk ↥A₀ := by
  obtain ⟨hA₀A, hB₀B, -, -, -, -, β, hβB, hβiff, hβsurj, -⟩ := h
  let β₁ : ↥A →* ↥B := (β.codRestrict B hβB)
  let q : ↥A →* ↥B ⧸ B₀.subgroupOf B := (QuotientGroup.mk' (B₀.subgroupOf B)).comp β₁
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk'_surjective (B₀.subgroupOf B) y
    obtain ⟨a, ha⟩ := hβsurj b hb
    refine ⟨a, ?_⟩
    show (QuotientGroup.mk' (B₀.subgroupOf B) (β₁ a)) = QuotientGroup.mk' _ ⟨b, hb⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (((β₁ a)⁻¹ * ⟨b, hb⟩ : ↥B) : V) = (β a * b⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, β₁, MonoidHom.codRestrict_apply, mul_inv,
        inv_inv]
    rw [this]
    exact B₀.inv_mem ha
  have hker : q.ker = A₀.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' (B₀.subgroupOf B) (β₁ a) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hβiff a
  have e := QuotientGroup.quotientKerEquivOfSurjective q hq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B₀.subgroupOf B)
  have hkerc : Nat.card ↥q.ker = Nat.card ↥A₀ := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀A).toEquiv
  have hB₀ : Nat.card ↥(B₀.subgroupOf B) = Nat.card ↥B₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀B).toEquiv
  rw [Nat.card_congr e.toEquiv, hkerc] at h1
  rw [hB₀] at h2
  have hc : Nat.card ↥A * Nat.card ↥B₀ = Nat.card ↥B * Nat.card ↥A₀ := by
    rw [h1, h2]
    ring
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne',
    ← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hc]

theorem rk_commSub_add_le {T I : Subgroup V} {τ : MulAut V} (hT : ∀ u ∈ T, τ u ∈ T)
    (hI : ∀ u ∈ I, τ u ∈ I) (hTI : T ⊓ I = ⊥) :
    rk ↥(commSub T (Subgroup.zpowers τ)) + rk ↥(commSub I (Subgroup.zpowers τ)) ≤
      rk ↥(commSub (T ⊔ I) (Subgroup.zpowers τ)) := by
  have hinv : ∀ {A : Subgroup V}, (∀ u ∈ A, τ u ∈ A) → ∀ x ∈ Subgroup.zpowers τ, ∀ u ∈ A, x u ∈ A := by
    intro A hA x hx u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hfin : ∀ n : ℕ, ∀ u ∈ A, (τ ^ n) u ∈ A := by
      intro n
      induction n with
      | zero => intro u hu; simpa using hu
      | succ n ih => intro u hu; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hA u hu)
    have hinvA : ∀ u ∈ A, τ⁻¹ u ∈ A := by
      intro u hu
      have hinj : Function.Injective (fun a : ↥A => (⟨τ a, hA a a.2⟩ : ↥A)) := by
        intro a b hab
        exact Subtype.ext (τ.injective (congrArg Subtype.val hab))
      obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨u, hu⟩
      have : τ a = u := congrArg Subtype.val ha
      rw [← this, MulAut.inv_apply_self]
      exact a.2
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · simpa using hfin n u hu
    · rw [zpow_neg, zpow_natCast]
      have hfin' : ∀ n : ℕ, ∀ u ∈ A, (τ⁻¹ ^ n) u ∈ A := by
        intro n
        induction n with
        | zero => intro u hu; simpa using hu
        | succ n ih => intro u hu; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hinvA u hu)
      rw [← inv_pow]
      exact hfin' n u hu
  have hTs := commSub_le_of_invariant (hinv hT)
  have hIs := commSub_le_of_invariant (hinv hI)
  have h1 : commSub T (Subgroup.zpowers τ) ⊓ commSub I (Subgroup.zpowers τ) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf hTs hIs).trans hTI.le)
  have h2 := rk_sup_add_rk_inf (commSub T (Subgroup.zpowers τ)) (commSub I (Subgroup.zpowers τ))
  rw [h1, rk_bot] at h2
  have h3 : commSub T (Subgroup.zpowers τ) ⊔ commSub I (Subgroup.zpowers τ) ≤
      commSub (T ⊔ I) (Subgroup.zpowers τ) :=
    sup_le (commSub_mono le_sup_left le_rfl) (commSub_mono le_sup_right le_rfl)
  have h4 := rk_mono h3
  omega

theorem sum_bound (hV : ∀ v : V, v ^ 2 = 1) (G : Subgroup (MulAut V)) (τ : MulAut V)
    (𝓘 : Set (Subgroup V)) (r m₀ : ℕ)
    (hG : ∀ I ∈ 𝓘, StableUnder G I ∧ ∀ J : Subgroup V, StableUnder G J → J ≤ I → J = ⊥ ∨ J = I)
    (hτ : ∀ I ∈ 𝓘, ∀ u ∈ I, τ u ∈ I) (hr : ∀ I ∈ 𝓘, rk ↥I = r)
    (hm : ∀ I ∈ 𝓘, m₀ ≤ rk ↥(commSub I (Subgroup.zpowers τ))) :
    ∃ k : ℕ, rk ↥(⨆ I ∈ 𝓘, I) = k * r ∧
      k * m₀ ≤ rk ↥(commSub (⨆ I ∈ 𝓘, I) (Subgroup.zpowers τ)) := by
  set S := ⨆ I ∈ 𝓘, I with hS
  let P : Subgroup V → Prop := fun T => T ≤ S ∧ StableUnder G T ∧ (∀ u ∈ T, τ u ∈ T) ∧
    ∃ k : ℕ, rk ↥T = k * r ∧ k * m₀ ≤ rk ↥(commSub T (Subgroup.zpowers τ))
  have hP0 : P ⊥ := ⟨bot_le, fun _ _ _ hu => by rw [(Subgroup.mem_bot).mp hu, map_one]; exact one_mem _,
    fun _ hu => by rw [(Subgroup.mem_bot).mp hu, map_one]; exact one_mem _, 0, by simp [rk_bot], by simp⟩
  have hstep : ∀ n : ℕ, ∀ T : Subgroup V, P T → rk ↥S - rk ↥T = n → P S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hT hn
      by_cases hTS : T = S
      · rw [← hTS]; exact hT
      · obtain ⟨hTle, hTG, hTτ, k, hk1, hk2⟩ := hT
        have hex : ∃ I ∈ 𝓘, ¬ I ≤ T := by
          by_contra hall
          push Not at hall
          exact hTS (le_antisymm hTle (iSup₂_le hall))
        obtain ⟨I, hI, hIT⟩ := hex
        obtain ⟨hIG, hIirr⟩ := hG I hI
        have hTI : T ⊓ I = ⊥ := by
          rcases hIirr (T ⊓ I) (stableUnder_inf hTG hIG) inf_le_right with h | h
          · exact h
          · exact absurd (h ▸ inf_le_left) hIT
        have hIS : I ≤ S := le_iSup₂_of_le I hI le_rfl
        have hrk := rk_sup_add_rk_inf T I
        rw [hTI, rk_bot, hr I hI] at hrk
        have hI0 : 0 < r := by
          rw [← hr I hI]
          by_contra h0
          push Not at h0
          have hbot : I = ⊥ := (rk_eq_zero_iff hV).mp (Nat.le_zero.mp h0)
          exact hIT (hbot ▸ bot_le)
        have hlt : rk ↥T < rk ↥(T ⊔ I) := by omega
        have hsS : rk ↥(T ⊔ I) ≤ rk ↥S := rk_mono (sup_le hTle hIS)
        refine ih (rk ↥S - rk ↥(T ⊔ I)) (by omega) (T ⊔ I) ⟨sup_le hTle hIS,
          stableUnder_sup hTG hIG, ?_, k + 1, ?_, ?_⟩ rfl
        · intro u hu
          obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
          rw [map_mul]
          exact Subgroup.mul_mem_sup (hTτ a ha) (hτ I hI b hb)
        · have : (k + 1) * r = k * r + r := by ring
          omega
        · have h1 := rk_commSub_add_le hTτ (hτ I hI) hTI
          have h2 := hm I hI
          have : (k + 1) * m₀ = k * m₀ + m₀ := by ring
          omega
  obtain ⟨-, -, -, k, hk⟩ := hstep (rk ↥S - rk ↥(⊥ : Subgroup V)) ⊥ hP0 rfl
  exact ⟨k, hk⟩

end Generic

section Specific

variable {W : Type} [CommGroup W] [Finite W]

theorem rkIdx_fixV_quotHom_le {C : Subgroup W} {t : MulAut W} (ht : t ∈ stabSub C) :
    rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨t, ht⟩))) ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hle : fixV (Subgroup.zpowers t) ≤
      (fixV (Subgroup.zpowers (quotHom C ⟨t, ht⟩))).comap (QuotientGroup.mk' C) := by
    intro w hw
    rw [Subgroup.mem_comap]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hwt : t w = w := hw t (Subgroup.mem_zpowers t)
    have htw : quotHom C ⟨t, ht⟩ (QuotientGroup.mk w) = QuotientGroup.mk w := by
      rw [quotHom_mk]
      exact congrArg _ hwt
    exact zpow_apply_eq_self htw k
  have hidx : rkIdx ((fixV (Subgroup.zpowers (quotHom C ⟨t, ht⟩))).comap (QuotientGroup.mk' C)) =
      rkIdx (fixV (Subgroup.zpowers (quotHom C ⟨t, ht⟩))) := by
    unfold rkIdx
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective C)]
  rw [← hidx]
  exact rkIdx_anti hle

theorem mParam_autSub_le_rk_commSub {V : Type} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)}
    {I : Subgroup V} {τ : MulAut V} (hτX : τ ∈ X) (hτI : τ ∈ stabSub I) (hτ2 : τ ^ 2 = 1)
    (hne : commSub I (Subgroup.zpowers τ) ≠ ⊥) :
    E3.mParam (autSub X I) ≤ rk ↥(commSub I (Subgroup.zpowers τ)) := by
  set τ₁ := resHom I ⟨τ, hτI⟩ with hτ₁
  have hτ₁X : τ₁ ∈ autSub X I := mem_autSub.mpr ⟨⟨τ, hτI⟩, hτX, rfl⟩
  have hstabτ : ∀ x ∈ Subgroup.zpowers τ, ∀ w ∈ I, x w ∈ I := by
    intro x hx w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((stabSub I).zpow_mem hτI k w).mpr hw
  have hrk := rk_commV_resHom hτI hstabτ
  have hA2 : IsPGroup 2 (Subgroup.zpowers τ₁) := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨1, Subtype.ext ?_⟩
    show (x : MulAut ↥I) ^ 2 ^ 1 = 1
    have hτ₁2 : τ₁ ^ 2 = 1 := by
      rw [hτ₁, ← map_pow]
      have : (⟨τ, hτI⟩ : stabSub I) ^ 2 = 1 := Subtype.ext (by simpa using hτ2)
      rw [this, map_one]
    rw [← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hτ₁2, one_zpow]
  have hA1 : Subgroup.zpowers τ₁ ≠ ⊥ := by
    intro h
    have hτ₁1 : τ₁ = 1 := by
      have : τ₁ ∈ Subgroup.zpowers τ₁ := Subgroup.mem_zpowers τ₁
      rw [h, Subgroup.mem_bot] at this
      exact this
    apply hne
    rw [commSub_eq_bot_iff]
    intro u hu x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hτu : τ u = u := by
      have := congrArg (fun φ : MulAut ↥I => ((φ ⟨u, hu⟩ : ↥I) : V)) hτ₁1
      simpa [hτ₁, resHom_apply] using this
    exact zpow_apply_eq_self hτu k
  have h1 := E3.mParam_le_rkIdx_fixV (Subgroup.zpowers_le.mpr hτ₁X) hA2 hA1
  have h2 := rk_commV_add_rk_fixV τ₁
  have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers τ₁))
  have hτ₁rk : rk ↥(commV (Subgroup.zpowers τ₁)) = rkIdx (fixV (Subgroup.zpowers τ₁)) := by omega
  exact h1.trans (hτ₁rk.symm.le.trans hrk.le)

end Specific

section Assembly

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def secKer (S C : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | g ∈ stabSub S ∧ ∀ u ∈ S, g u * u⁻¹ ∈ C}
  one_mem' := ⟨(stabSub S).one_mem, fun u _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(stabSub S).mul_mem ha1 hb1, fun u hu => ?_⟩
    have hbu : b u ∈ S := (hb1 u).mpr hu
    have he : (a * b) u * u⁻¹ = (a (b u) * (b u)⁻¹) * (b u * u⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [he]
    exact C.mul_mem (ha2 _ hbu) (hb2 u hu)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨(stabSub S).inv_mem ha1, fun u hu => ?_⟩
    have hu' : a⁻¹ u ∈ S := by
      have := (ha1 (a⁻¹ u)).mp
      rw [MulAut.apply_inv_self] at this
      exact this hu
    have h := ha2 _ hu'
    rw [MulAut.apply_inv_self] at h
    have he : a⁻¹ u * u⁻¹ = (u * (a⁻¹ u)⁻¹)⁻¹ := by group
    rw [he]
    exact C.inv_mem h

omit [Finite W] in
theorem conj_mem_secKer {S C : Subgroup W} {g k : MulAut W} (hgS : g ∈ stabSub S)
    (hgC : ∀ c ∈ C, g c ∈ C) (hk : k ∈ secKer S C) : g * k * g⁻¹ ∈ secKer S C := by
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨(stabSub S).mul_mem ((stabSub S).mul_mem hgS hk1) ((stabSub S).inv_mem hgS), ?_⟩
  intro u hu
  have hu' : g⁻¹ u ∈ S := ((stabSub S).inv_mem hgS u).mpr hu
  have h := hgC _ (hk2 _ hu')
  have he : g (k (g⁻¹ u) * (g⁻¹ u)⁻¹) = (g * k * g⁻¹) u * u⁻¹ := by
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.apply_inv_self]
  rwa [he] at h

theorem not_commSub_zpowers_le {L : Subgroup (MulAut W)} {t : MulAut W}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hLt : L.map (MulAut.conj t).toMonoidHom = L)
    (hLc : ¬ ∀ x ∈ L, t * x = x * t) {S C : Subgroup W} (hLS : ∀ l ∈ L, l ∈ stabSub S)
    (hLC : ∀ l ∈ L, ∀ c ∈ C, l c ∈ C) (htS : t ∈ stabSub S) (hL : ¬ commSub S L ≤ C) :
    ¬ commSub S (Subgroup.zpowers t) ≤ C := by
  intro ht
  apply hL
  have htK : t ∈ secKer S C := ⟨htS, fun u hu => ht (Subgroup.subset_closure
    ⟨t, Subgroup.mem_zpowers t, u, hu, rfl⟩)⟩
  have hnorm : ∀ b ∈ Subgroup.zpowers t, ∀ l ∈ L, b * l * b⁻¹ ∈ L := by
    have htn : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro l
      constructor
      · intro hl
        have : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := ⟨l, hl, rfl⟩
        rwa [hLt] at this
      · intro hl
        rw [← hLt] at hl
        obtain ⟨l', hl', hll'⟩ := hl
        have : l = l' := by
          have h2 : t * l' * t⁻¹ = t * l * t⁻¹ := hll'
          exact (by simpa using h2 : l' = l).symm
        rw [this]
        exact hl'
    intro b hb l hl
    have hbn := (Subgroup.zpowers_le.mpr htn) hb
    exact (Subgroup.mem_normalizer_iff.mp hbn l).mp hl
  have hnc : ¬ Subgroup.zpowers t ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
    intro hc
    apply hLc
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_zpowers t)) x hx).symm
  have hcomm := CFSG.Quasithin.B113.commutator_comp_eq_of_normalizes hLq hnorm hnc
  have hLK : L ≤ secKer S C := by
    rw [← hcomm, Subgroup.commutator_le]
    intro l hl b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hb' : t ^ k ∈ secKer S C := (secKer S C).zpow_mem htK k
    have h1 : l * t ^ k * l⁻¹ ∈ secKer S C := conj_mem_secKer (hLS l hl) (hLC l hl) hb'
    have h2 := (secKer S C).mul_mem h1 ((secKer S C).inv_mem hb')
    simpa [commutatorElement_def] using h2
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨l, hl, u, hu, rfl⟩
  exact (hLK hl).2 u hu

omit [Finite W] in
theorem map_mk_stable_irr {H : Subgroup (MulAut W)} (hstab : H ≤ stabSub (fixV H))
    {I : Subgroup W} (hI : I ∈ irrSet H) :
    StableUnder (autQuot H (fixV H)) (I.map (QuotientGroup.mk' (fixV H))) ∧
      ∀ J : Subgroup (W ⧸ fixV H), StableUnder (autQuot H (fixV H)) J →
        J ≤ I.map (QuotientGroup.mk' (fixV H)) → J = ⊥ ∨ J = I.map (QuotientGroup.mk' (fixV H)) := by
  set C := fixV H with hC
  have hirr := isIrrOn_sup_fixV hI
  refine ⟨?_, ?_⟩
  · intro φ hφ v hv
    obtain ⟨g, hgH, rfl⟩ := mem_autQuot.mp hφ
    obtain ⟨i, hi, rfl⟩ := hv
    exact ⟨g.1 i, hI.2.2.1 g.1 hgH i hi, by simp [quotHom_mk]⟩
  · intro J hJ hJI
    have hJs : StableUnder H (J.comap (QuotientGroup.mk' C)) := by
      intro h hh w hw
      rw [Subgroup.mem_comap] at hw ⊢
      have := hJ (quotHom C ⟨h, hstab hh⟩) (mem_autQuot.mpr ⟨⟨h, hstab hh⟩, hh, rfl⟩) _ hw
      simpa [quotHom_mk] using this
    have hCle : C ≤ J.comap (QuotientGroup.mk' C) := by
      intro c hc
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff c).mpr hc]
      exact J.one_mem
    have hle : J.comap (QuotientGroup.mk' C) ≤ I ⊔ C := by
      have := Subgroup.comap_mono (f := QuotientGroup.mk' C) hJI
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    rcases hirr.2.2.2 _ hJs hCle hle with h | h
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) J, h,
        QuotientGroup.map_mk'_self]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) J, h,
        Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]

theorem rk_map_mk_eq (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {I J : Subgroup W} (hI : I ∈ irrSet H) (hJ : J ∈ irrSet H) :
    rk ↥(I.map (QuotientGroup.mk' (fixV H))) = rk ↥(J.map (QuotientGroup.mk' (fixV H))) := by
  obtain ⟨h1, -, hHY, hn, hnorm, hne⟩ := h_facts hL hH
  obtain ⟨g, hg, hsec⟩ := ((w4Lem12_5_holds W hW Y hO hB H hne hHY hnorm).2 L hL h1).1.2 I hI J hJ
  have hrk := secIsoOn_rk hsec
  set C := fixV H with hC
  have hgH : ∀ x ∈ H, g * x * g⁻¹ ∈ H := hn g hg
  have hgH' : ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
    intro x hx
    simpa using hn g⁻¹ (Y.inv_mem hg) x hx
  have hCg : C.map g.toMonoidHom = C := map_fixV_of_normalizes hgH hgH'
  have hIg : rk ↥(I.map g.toMonoidHom ⊔ C) = rk ↥(I ⊔ C) := by
    have : I.map g.toMonoidHom ⊔ C = (I ⊔ C).map g.toMonoidHom := by rw [Subgroup.map_sup, hCg]
    rw [this]
    unfold rk
    rw [Subgroup.card_map_of_injective g.injective]
  have hmk : ∀ A : Subgroup W, rk ↥(A.map (QuotientGroup.mk' C)) + rk ↥C = rk ↥(A ⊔ C) := by
    intro A
    have h := rk_map_mk (A ⊔ C) C
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      inf_eq_right.mpr (le_sup_right : C ≤ A ⊔ C)] at h
  have h2 := hmk I
  have h3 := hmk J
  omega

theorem exists_irrSet_L_sup_eq {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {I : Subgroup W} (hI : I ∈ irrSet H)
    (hLI : ¬ commSub I L ≤ fixV H)
    (huniqI : ∀ X ∈ conjSet L Y, ¬ commSub I X ≤ fixV H → X = L) :
    ∃ J ∈ irrSet L, J ≤ I ∧ J ⊔ fixV H = I ⊔ fixV H := by
  set C := fixV H with hC
  obtain ⟨-, hLH, -, -, -, -⟩ := h_facts hL hH
  have hQ : QuadTrivial L := quadTrivial_of_commutator_eq_top hL.2.2.1
  have hIL : StableUnder L I := fun x hx u hu => hI.2.2.1 x (hLH hx) u hu
  have hne : commSub I L ≠ ⊥ := fun h => hLI (h ▸ bot_le)
  obtain ⟨J, hJ, hJI⟩ := exists_mem_irrSet_le hQ hIL hne
  refine ⟨J, hJ, hJI, ?_⟩
  have hJs : StableUnder H (J ⊔ C) := by
    intro h hh
    rw [hH, iSup_subtype'] at hh
    refine Subgroup.iSup_induction (fun X : conjSet L Y => (X : Subgroup (MulAut W)))
      (C := fun h => ∀ u ∈ J ⊔ C, h u ∈ J ⊔ C) hh ?_ ?_ ?_
    · intro X x hx u hu
      obtain ⟨-, hXH, -⟩ := conjSet_facts hL hH X.2
      obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul, hc x (hXH hx)]
      refine (J ⊔ C).mul_mem ?_ (le_sup_right (α := Subgroup W) hc)
      by_cases hXL : (X : Subgroup (MulAut W)) = L
      · have hxL : x ∈ L := hXL ▸ hx
        exact le_sup_left (α := Subgroup W) (hJ.2.2.1 x hxL a ha)
      · have hXI : commSub I X ≤ C := by
          by_contra h
          exact hXL (huniqI X X.2 h)
        have hxa : x a * a⁻¹ ∈ C := hXI (Subgroup.subset_closure ⟨x, hx, a, hJI ha, rfl⟩)
        have he : x a = (x a * a⁻¹) * a := by group
        rw [he]
        exact (J ⊔ C).mul_mem (le_sup_right (α := Subgroup W) hxa)
          (le_sup_left (α := Subgroup W) ha)
    · intro u hu
      simpa using hu
    · intro a b ha hb u hu
      rw [MulAut.mul_apply]
      exact ha _ (hb u hu)
  have hirr := isIrrOn_sup_fixV hI
  rcases hirr.2.2.2 _ hJs le_sup_right (sup_le_sup_right hJI C) with h | h
  · exfalso
    exact not_le_fixV_of_mem_irrSet hJ ((le_sup_left.trans h.le).trans
      (fun w hw x hx => hw x (hLH hx)))
  · exact h

theorem commV_autQuot_eq_iSup (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X) :
    commV (autQuot L (fixV H)) =
      ⨆ I ∈ {I : Subgroup W | I ∈ irrSet H ∧ ¬ commSub I L ≤ fixV H},
        I.map (QuotientGroup.mk' (fixV H)) := by
  obtain ⟨h1, hLH, hHY, hn, hnorm, hne⟩ := h_facts hL hH
  set C := fixV H with hC
  have hstab : Y ≤ stabSub C := le_stabSub_fixV hn
  have hLstab : L ≤ stabSub C := (hLH.trans hHY).trans hstab
  have hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := conj_mem_of_eq_biSup_conj hL h1
  rw [commV_autQuot hLstab]
  set 𝓘 := {I : Subgroup W | I ∈ irrSet H ∧ ¬ commSub I L ≤ C} with h𝓘
  apply le_antisymm
  · have htop : (⨆ I ∈ irrSet H, I) = ⊤ :=
      ((w4Lem12_5_holds W hW Y hO hB H hne hHY hnorm).2 L hL h1).1.1
    have hle : commV L ≤ (⨆ I ∈ 𝓘, I) ⊔ C := by
      rw [commV_eq_commSub, ← htop, commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, v, hv, rfl⟩
      rw [iSup_subtype'] at hv
      refine Subgroup.iSup_induction (fun I : irrSet H => (I : Subgroup W))
        (C := fun v => x v * v⁻¹ ∈ (⨆ I ∈ 𝓘, I) ⊔ C) hv ?_ ?_ ?_
      · intro I v hv
        by_cases hI : commSub (I : Subgroup W) L ≤ C
        · exact le_sup_right (α := Subgroup W) (hI (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩))
        · have hle' : (I : Subgroup W) ≤ ⨆ J ∈ 𝓘, J := le_iSup₂_of_le (I : Subgroup W) ⟨I.2, hI⟩ le_rfl
          exact le_sup_left (α := Subgroup W) (hle' ((I : Subgroup W).mul_mem
            (I.2.2.2.1 x (hLH hx) v hv) ((I : Subgroup W).inv_mem hv)))
      · simp
      · intro a b ha hb
        have he : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
          rw [map_mul, mul_inv, mul_mul_mul_comm]
        rw [he]
        exact Subgroup.mul_mem _ ha hb
    have h2 := Subgroup.map_mono (f := QuotientGroup.mk' C) hle
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h2
    simpa only [Subgroup.map_iSup] using h2
  · refine iSup₂_le fun I hI => ?_
    obtain ⟨hIH, hIL⟩ := hI
    have hirr := isIrrOn_sup_fixV hIH
    have hJs : StableUnder H (commSub I L ⊔ C) :=
      stableUnder_sup (stableUnder_commSub hLn hIH.2.2.1)
        (stableUnder_fixV fun y hy h hh => hn y (hHY hy) h hh)
    have hJle : commSub I L ⊔ C ≤ I ⊔ C :=
      sup_le_sup_right (commSub_le_of_invariant fun x hx u hu => hIH.2.2.1 x (hLH hx) u hu) C
    have hJeq : commSub I L ⊔ C = I ⊔ C := by
      rcases hirr.2.2.2 _ hJs le_sup_right hJle with h | h
      · exact absurd (le_sup_left.trans h.le) hIL
      · exact h
    calc I.map (QuotientGroup.mk' C) ≤ (I ⊔ C).map (QuotientGroup.mk' C) :=
          Subgroup.map_mono le_sup_left
      _ = (commSub I L).map (QuotientGroup.mk' C) := by
          rw [← hJeq, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
      _ ≤ (commV L).map (QuotientGroup.mk' C) :=
          Subgroup.map_mono (by rw [commV_eq_commSub]; exact commSub_mono le_top le_rfl)

theorem exists_mul_le_rkIdx (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hB : IsBasicModule Y) (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X)
    {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hfix : ∀ I ∈ irrSet H, I.map t.toMonoidHom = I)
    (hLt : L.map (MulAut.conj t).toMonoidHom = L) (hLc : ¬ ∀ x ∈ L, t * x = x * t)
    (huniq : ∀ I ∈ irrSet H, ∀ X ∈ conjSet L Y, ∀ X' ∈ conjSet L Y,
      ¬ commSub I X ≤ fixV H → ¬ commSub I X' ≤ fixV H → X = X') :
    ∃ I ∈ irrSet L,
      (E3.mParam (autSub (autQuot Y (fixV H)) (I.map (QuotientGroup.mk' (fixV H)))) : ℚ) *
          ((rk ↥(commV (autQuot L (fixV H))) : ℚ) /
            (rk ↥(I.map (QuotientGroup.mk' (fixV H))) : ℚ)) ≤
        rkIdx (fixV (Subgroup.zpowers t)) := by
  obtain ⟨h1, hLH, hHY, hn, hnorm, hne⟩ := h_facts hL hH
  have hstab : Y ≤ stabSub (fixV H) := le_stabSub_fixV hn
  have hHstab : H ≤ stabSub (fixV H) := hHY.trans hstab
  have hLstab : L ≤ stabSub (fixV H) := hLH.trans hHstab
  have hcomm := commV_autQuot_eq_iSup hW hO hB hL hH
  have hcV := commV_autQuot hLstab
  set C := fixV H with hC
  have htC : t ∈ stabSub C := hstab ht
  set τ : MulAut (W ⧸ C) := quotHom C ⟨t, htC⟩ with hτ
  have hτY : τ ∈ autQuot Y C := mem_autQuot.mpr ⟨⟨t, htC⟩, ht, rfl⟩
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hτ2 : τ ^ 2 = 1 := by
    rw [hτ, ← map_pow]
    have : (⟨t, htC⟩ : stabSub C) ^ 2 = 1 := Subtype.ext (by simpa using ht2')
    rw [this, map_one]
  have hττ : ∀ u : W ⧸ C, τ (τ u) = u := by
    intro u
    rw [← MulAut.mul_apply, ← pow_two, hτ2, MulAut.one_apply]
  have hV : ∀ v : W ⧸ C, v ^ 2 = 1 := by
    intro v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective C v
    rw [← map_pow, hW, map_one]
  have htS : ∀ I ∈ irrSet H, t ∈ stabSub I := by
    intro I hI u
    have hm := hfix I hI
    constructor
    · intro hu
      rw [← hm] at hu
      obtain ⟨v, hv, hvu⟩ := hu
      have hvu' : t v = t u := hvu
      rwa [← t.injective hvu']
    · intro hu
      rw [← hm]
      exact ⟨u, hu, rfl⟩
  have hLS : ∀ I ∈ irrSet H, ∀ l ∈ L, l ∈ stabSub I := by
    intro I hI l hl u
    refine ⟨fun hu => ?_, fun hu => hI.2.2.1 l (hLH hl) u hu⟩
    have := hI.2.2.1 l⁻¹ (H.inv_mem (hLH hl)) _ hu
    rwa [MulAut.inv_apply_self] at this
  have hLC : ∀ l ∈ L, ∀ c ∈ C, l c ∈ C := fun l hl c hc => by rw [hc l (hLH hl)]; exact hc
  set S := {I : Subgroup W | I ∈ irrSet H ∧ ¬ commSub I L ≤ C} with hS
  have hSne : S.Nonempty := by
    by_contra hSe
    rw [Set.not_nonempty_iff_eq_empty] at hSe
    rw [hSe, iSup_emptyset] at hcomm
    have hbot : (commV L).map (QuotientGroup.mk' C) = ⊥ := by rw [← hcV, hcomm]
    apply hLc
    intro x hx
    have hx1 : x = 1 := by
      refine eq_one_of_mem_fixV_quot hW hO hB hL hH (hHY (hLH hx)) fun w => ?_
      have hmem : QuotientGroup.mk' C (x w * w⁻¹) ∈ (commV L).map (QuotientGroup.mk' C) :=
        Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨x, hx, w, rfl⟩)
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    rw [hx1, mul_one, one_mul]
  set f : Subgroup W → ℕ :=
    fun I => E3.mParam (autSub (autQuot Y C) (I.map (QuotientGroup.mk' C))) with hf
  obtain ⟨I₀, hI₀S, hI₀f⟩ := Nat.sInf_mem (hSne.image f)
  set m₀ := sInf (f '' S) with hm₀
  have hmin : ∀ I ∈ S, m₀ ≤ f I := fun I hI => Nat.sInf_le ⟨I, hI, rfl⟩
  have hG : ∀ I' ∈ (fun I => I.map (QuotientGroup.mk' C)) '' S,
      StableUnder (autQuot H C) I' ∧ ∀ J : Subgroup (W ⧸ C), StableUnder (autQuot H C) J →
        J ≤ I' → J = ⊥ ∨ J = I' := by
    rintro _ ⟨I, hI, rfl⟩
    exact map_mk_stable_irr hHstab hI.1
  have hτI : ∀ I' ∈ (fun I => I.map (QuotientGroup.mk' C)) '' S, ∀ u ∈ I', τ u ∈ I' := by
    rintro _ ⟨I, hI, rfl⟩ _ ⟨i, hi, rfl⟩
    refine ⟨t i, ((htS I hI.1) i).mpr hi, ?_⟩
    rfl
  have hr : ∀ I' : Subgroup (W ⧸ C), I' ∈ (fun I => I.map (QuotientGroup.mk' C)) '' S →
      rk ↥I' = rk ↥(I₀.map (QuotientGroup.mk' C)) := by
    rintro _ ⟨I, hI, rfl⟩
    exact rk_map_mk_eq hW hO hB hL hH hI.1 hI₀S.1
  have hm : ∀ I' ∈ (fun I => I.map (QuotientGroup.mk' C)) '' S,
      m₀ ≤ rk ↥(commSub I' (Subgroup.zpowers τ)) := by
    rintro _ ⟨I, hI, rfl⟩
    refine (hmin I hI).trans ?_
    have hτstab : τ ∈ stabSub (I.map (QuotientGroup.mk' C)) := by
      intro u
      refine ⟨fun hu => ?_, fun hu => hτI _ ⟨I, hI, rfl⟩ u hu⟩
      have h2 := hτI _ ⟨I, hI, rfl⟩ _ hu
      rwa [hττ] at h2
    have hne' : commSub (I.map (QuotientGroup.mk' C)) (Subgroup.zpowers τ) ≠ ⊥ := by
      intro h0
      rw [commSub_eq_bot_iff] at h0
      apply not_commSub_zpowers_le hL.2.2 hLt hLc (hLS I hI.1) hLC (htS I hI.1) hI.2
      have htK : t ∈ secKer I C := by
        refine ⟨htS I hI.1, fun u hu => ?_⟩
        have h3 := h0 ⟨u, hu, rfl⟩ τ (Subgroup.mem_zpowers τ)
        rw [hτ, QuotientGroup.mk'_apply, quotHom_mk] at h3
        exact (mk_eq_mk_iff _ _).mp h3
      have hle : Subgroup.zpowers t ≤ secKer I C := Subgroup.zpowers_le.mpr htK
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, u, hu, rfl⟩
      exact (hle hx).2 u hu
    exact mParam_autSub_le_rk_commSub hτY hτstab hτ2 hne'
  obtain ⟨k, hk1, hk2⟩ := sum_bound hV (autQuot H C) τ ((fun I => I.map (QuotientGroup.mk' C)) '' S)
    (rk ↥(I₀.map (QuotientGroup.mk' C))) m₀ hG hτI hr hm
  have h𝓘 : (⨆ I' ∈ (fun I => I.map (QuotientGroup.mk' C)) '' S, I') = commV (autQuot L C) := by
    rw [hcomm]
    apply le_antisymm
    · refine iSup₂_le ?_
      rintro _ ⟨I, hI, rfl⟩
      exact le_iSup₂_of_le I hI le_rfl
    · refine iSup₂_le fun I hI => ?_
      exact le_iSup₂_of_le (I.map (QuotientGroup.mk' C)) ⟨I, hI, rfl⟩ le_rfl
  rw [h𝓘] at hk1 hk2
  have hchain : k * m₀ ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    refine hk2.trans ?_
    have h3 : rk ↥(commSub (commV (autQuot L C)) (Subgroup.zpowers τ)) ≤
        rk ↥(commV (Subgroup.zpowers τ)) := by
      refine rk_mono ?_
      rw [commV_eq_commSub (Subgroup.zpowers τ)]
      exact commSub_mono le_top le_rfl
    have h4 := rk_commV_add_rk_fixV τ
    have h5 := rk_add_rkIdx (fixV (Subgroup.zpowers τ))
    have h6 := rkIdx_fixV_quotHom_le htC
    rw [← hτ] at h6
    omega
  have huniqI₀ : ∀ X ∈ conjSet L Y, ¬ commSub I₀ X ≤ C → X = L := by
    intro X hX hXI
    refine huniq I₀ hI₀S.1 X hX L ⟨1, Y.one_mem, ?_⟩ hXI hI₀S.2
    ext x
    simp
  obtain ⟨J, hJ, -, hJC⟩ := exists_irrSet_L_sup_eq hL hH hI₀S.1 hI₀S.2 huniqI₀
  rw [← hC] at hJC
  have hJmap : J.map (QuotientGroup.mk' C) = I₀.map (QuotientGroup.mk' C) := by
    have := congrArg (Subgroup.map (QuotientGroup.mk' C)) hJC
    rwa [Subgroup.map_sup, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      sup_bot_eq] at this
  refine ⟨J, hJ, ?_⟩
  have hfI₀ : E3.mParam (autSub (autQuot Y C) (I₀.map (QuotientGroup.mk' C))) = m₀ := hI₀f
  rw [hJmap, hfI₀, hk1]
  rcases Nat.eq_zero_or_pos (rk ↥(I₀.map (QuotientGroup.mk' C))) with hr0 | hr0
  · rw [hr0]
    simp
  · have hr' : ((rk ↥(I₀.map (QuotientGroup.mk' C)) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0.ne'
    rw [Nat.cast_mul, mul_div_assoc, div_self hr', mul_one, mul_comm]
    exact_mod_cast hchain

end Assembly

end CFSG.LocalAnalysis.WeakClosure81
