module

public import CFSG.Quasithin.MS93.S512LGrp
public import CFSG.Quasithin.MS93.S512NMod
public import CFSG.Quasithin.MS93.S38OffHatMod
public import CFSG.Quasithin.MS93.S36SpESec

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin
open scoped commutatorElement

namespace S512L

section Form

variable {Γ : Type} [Group Γ] {Ga Vo B V₀ : Subgroup Γ} {S : Type} [CommGroup S]
  {p : ↥Vo →* S} {ρ : ↥Ga →* MulAut S}

theorem exists_mem_of_irr (hs : S36E.SecData Ga Vo (Vo ⊓ B) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤) (hV₀ : V₀ ≤ Vo)
    (hV₀n : Ga ≤ Subgroup.normalizer (V₀ : Set Γ)) (hV₀B : ¬ V₀ ≤ B) (s : S) :
    ∃ v : ↥Vo, (v : Γ) ∈ V₀ ∧ p v = s := by
  have hinv : S512N.IsInv ρ ((V₀.subgroupOf Vo).map p) := by
    rintro g _ ⟨v, hv, rfl⟩
    have hgv : (g : Γ) * v * (g : Γ)⁻¹ ∈ Vo := S36E.conj_mem hs.hMA g.2 v.2
    exact ⟨⟨_, hgv⟩, Subgroup.mem_subgroupOf.2 (S36E.conj_mem hV₀n g.2
      (Subgroup.mem_subgroupOf.1 hv)), (hs.conj g v hgv).symm⟩
  have hne : (V₀.subgroupOf Vo).map p ≠ ⊥ := by
    intro hbot
    apply hV₀B
    intro v hv
    have : p ⟨v, hV₀ hv⟩ ∈ (V₀.subgroupOf Vo).map p :=
      ⟨⟨v, hV₀ hv⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, hs.ker] at this
    exact this.2
  have hs' : s ∈ (V₀.subgroupOf Vo).map p := by
    rw [hirr _ hne hinv]
    exact Subgroup.mem_top s
  obtain ⟨v, hv, rfl⟩ := hs'
  exact ⟨v, Subgroup.mem_subgroupOf.1 hv, rfl⟩

theorem commute_of_mem_fixV (hs : S36E.SecData Ga Vo (Vo ⊓ B) S p ρ) (hV₀G : V₀ ≤ Ga)
    (hV₀n : Ga ≤ Subgroup.normalizer (V₀ : Set Γ)) (hcomm : ⁅V₀, V₀ ⊓ B⁆ = ⊥)
    (hcen : ∀ v ∈ V₀, ∀ w ∈ V₀, ∀ g ∈ Ga, g * ⁅v, w⁆ = ⁅v, w⁆ * g)
    (hsurj : ∀ s : S, ∃ v : ↥Vo, (v : Γ) ∈ V₀ ∧ p v = s)
    {A : Subgroup (MulAut S)} (hA : A ≤ ρ.range) {x w : ↥Vo} (hx : (x : Γ) ∈ V₀)
    (hw : (w : Γ) ∈ V₀) (hpx : p x ∈ fixV A) (hpw : p w ∈ commV A) :
    (x : Γ) * w = w * x := by
  have hxB : ∀ b ∈ V₀ ⊓ B, (x : Γ) * b = b * x := fun b hb => by
    have h1 := Subgroup.commutator_mem_commutator hx hb
    rwa [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  set C : Subgroup Γ := V₀ ⊓ Subgroup.centralizer {(x : Γ)} with hC
  have key : ∀ w' : ↥Vo, (w' : Γ) ∈ V₀ → p w' ∈ (C.subgroupOf Vo).map p →
      (x : Γ) * w' = w' * x := by
    rintro w' hw' ⟨c, hc, hcw⟩
    have hc : (c : Γ) ∈ C := hc
    have hb : (w' : Γ) * (c : Γ)⁻¹ ∈ V₀ ⊓ B :=
      Subgroup.mem_inf.2 ⟨mul_mem hw' (inv_mem hc.1), ((hs.eq_iff w' c).1 hcw.symm).2⟩
    have hxc : (x : Γ) * c = c * x := (Subgroup.mem_centralizer_singleton_iff.1 hc.2).symm
    have h := Commute.mul_right (hxB _ hb : Commute (x : Γ) ((w' : Γ) * (c : Γ)⁻¹))
      (hxc : Commute (x : Γ) c)
    rwa [inv_mul_cancel_right] at h
  refine key w hw ((Subgroup.closure_le _).2 ?_ hpw)
  rintro _ ⟨a, ha, s, rfl⟩
  obtain ⟨d, rfl⟩ := hA ha
  obtain ⟨u, hu, rfl⟩ := hsurj s
  have hdu : (d : Γ) * u * (d : Γ)⁻¹ ∈ Vo := S36E.conj_mem hs.hMA d.2 u.2
  have hduV : (d : Γ) * u * (d : Γ)⁻¹ ∈ V₀ := S36E.conj_mem hV₀n d.2 hu
  refine ⟨⟨_, hdu⟩ * u⁻¹, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
    ⟨mul_mem hduV (inv_mem hu), ?_⟩), ?_⟩
  swap
  · rw [map_mul, map_inv, ← hs.conj d u hdu]
  have hdx : (d : Γ) * x * (d : Γ)⁻¹ ∈ Vo := S36E.conj_mem hs.hMA d.2 x.2
  have hpd : p ⟨_, hdx⟩ = p x := by rw [← hs.conj d x hdx]; exact hpx _ ha
  set b := (d : Γ) * x * (d : Γ)⁻¹ * (x : Γ)⁻¹ with hbdef
  have hb : b ∈ V₀ ⊓ B := Subgroup.mem_inf.2
    ⟨mul_mem (S36E.conj_mem hV₀n d.2 hx) (inv_mem hx), ((hs.eq_iff ⟨_, hdx⟩ x).1 hpd).2⟩
  set y := (d : Γ) * u * (d : Γ)⁻¹ with hydef
  have hby : ⁅b, y⁆ = 1 := by
    have h1 := Subgroup.commutator_mem_commutator hduV hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact commutatorElement_eq_one_iff_mul_comm.2 h1.symm
  have e1 : ⁅b * x, y⁆ = ⁅(x : Γ), y⁆ * ⁅b, y⁆ :=
    commutatorElement_mul_left_of_comm (hcen _ hx _ hduV _ (hV₀G hb.1))
  have e2 : b * x = (d : Γ) * x * (d : Γ)⁻¹ := by rw [hbdef]; group
  have e3 : ⁅(d : Γ) * x * (d : Γ)⁻¹, y⁆ = (d : Γ) * ⁅(x : Γ), (u : Γ)⁆ * (d : Γ)⁻¹ := by
    rw [hydef]
    simp only [commutatorElement_def]
    group
  have e4 : (d : Γ) * ⁅(x : Γ), (u : Γ)⁆ * (d : Γ)⁻¹ = ⁅(x : Γ), (u : Γ)⁆ := by
    rw [hcen _ hx _ hu _ d.2, mul_inv_cancel_right]
  have hxy : ⁅(x : Γ), y⁆ = ⁅(x : Γ), (u : Γ)⁆ := by
    rw [← e4, ← e3, ← e2, e1, hby, mul_one]
  have hxu : ⁅(x : Γ), (u : Γ)⁻¹⁆ = ⁅(x : Γ), (u : Γ)⁆⁻¹ := by
    have hc : Commute (u : Γ) ⁅(x : Γ), (u : Γ)⁆ := hcen _ hx _ hu _ (hV₀G hu)
    have e : ⁅(x : Γ), (u : Γ)⁻¹⁆ = (u : Γ)⁻¹ * (⁅(x : Γ), (u : Γ)⁆⁻¹ * u) := by
      simp only [commutatorElement_def]
      group
    rw [e, ← hc.inv_right.eq, inv_mul_cancel_left]
  have e5 : ⁅(x : Γ), y * (u : Γ)⁻¹⁆ = ⁅(x : Γ), y⁆ * ⁅(x : Γ), (u : Γ)⁻¹⁆ :=
    commutatorElement_mul_right_of_comm (hcen _ hx _ (inv_mem hu) _ (hV₀G hduV))
  have h1 : ⁅(x : Γ), y * (u : Γ)⁻¹⁆ = 1 := by rw [e5, hxy, hxu, mul_inv_cancel]
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

theorem commute_of_mem_map_fixV (hs : S36E.SecData Ga Vo (Vo ⊓ B) S p ρ) (hV₀G : V₀ ≤ Ga)
    (hV₀n : Ga ≤ Subgroup.normalizer (V₀ : Set Γ)) (hcomm : ⁅V₀, V₀ ⊓ B⁆ = ⊥)
    (hcen : ∀ v ∈ V₀, ∀ w ∈ V₀, ∀ g ∈ Ga, g * ⁅v, w⁆ = ⁅v, w⁆ * g)
    (hsurj : ∀ s : S, ∃ v : ↥Vo, (v : Γ) ∈ V₀ ∧ p v = s)
    {A : Subgroup (MulAut S)} (hA : A ≤ ρ.range) (g : ↥Ga) {x w : ↥Vo} (hx : (x : Γ) ∈ V₀)
    (hw : (w : Γ) ∈ V₀) (hpx : p x ∈ (fixV A).map (ρ g).toMonoidHom)
    (hpw : p w ∈ (commV A).map (ρ g).toMonoidHom) :
    (x : Γ) * w = w * x := by
  have hx₁ : ((g⁻¹ : ↥Ga) : Γ) * x * ((g⁻¹ : ↥Ga) : Γ)⁻¹ ∈ Vo :=
    S36E.conj_mem hs.hMA (g⁻¹).2 x.2
  have hw₁ : ((g⁻¹ : ↥Ga) : Γ) * w * ((g⁻¹ : ↥Ga) : Γ)⁻¹ ∈ Vo :=
    S36E.conj_mem hs.hMA (g⁻¹).2 w.2
  have hback : ∀ {t : S} {X : Subgroup S}, t ∈ X.map (ρ g).toMonoidHom → ρ g⁻¹ t ∈ X := by
    rintro _ X ⟨s, hs', rfl⟩
    rw [map_inv]
    show (ρ g)⁻¹ ((ρ g) s) ∈ X
    rw [MulAut.inv_apply_self]
    exact hs'
  have h1 := commute_of_mem_fixV hs hV₀G hV₀n hcomm hcen hsurj hA (x := ⟨_, hx₁⟩)
    (w := ⟨_, hw₁⟩) (S36E.conj_mem hV₀n (g⁻¹).2 hx) (S36E.conj_mem hV₀n (g⁻¹).2 hw)
    (by rw [← hs.conj g⁻¹ x hx₁]; exact hback hpx) (by rw [← hs.conj g⁻¹ w hw₁]; exact hback hpw)
  simp only [Subgroup.coe_inv, inv_inv] at h1
  calc (x : Γ) * w = g * (((g : Γ)⁻¹ * x * g) * ((g : Γ)⁻¹ * w * g)) * (g : Γ)⁻¹ := by group
    _ = g * (((g : Γ)⁻¹ * w * g) * ((g : Γ)⁻¹ * x * g)) * (g : Γ)⁻¹ := by rw [h1]
    _ = w * x := by group

theorem commutator_eq_bot_of_commute (hs : S36E.SecData Ga Vo (Vo ⊓ B) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤) (hV₀ : V₀ ≤ Vo)
    (hV₀n : Ga ≤ Subgroup.normalizer (V₀ : Set Γ)) (hcomm : ⁅V₀, V₀ ⊓ B⁆ = ⊥) {x : ↥Vo}
    (hx : (x : Γ) ∈ V₀) (hpx : p x ≠ 1) (hxc : ∀ w ∈ V₀, (x : Γ) * w = w * x) :
    ⁅V₀, V₀⁆ = ⊥ := by
  set Z : Subgroup Γ := V₀ ⊓ Subgroup.centralizer (V₀ : Set Γ) with hZ
  have hinv : S512N.IsInv ρ ((Z.subgroupOf Vo).map p) := by
    rintro g _ ⟨c, hc, rfl⟩
    have hc : (c : Γ) ∈ Z := hc
    have hgc : (g : Γ) * c * (g : Γ)⁻¹ ∈ Vo := S36E.conj_mem hs.hMA g.2 c.2
    refine ⟨⟨_, hgc⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2
      ⟨S36E.conj_mem hV₀n g.2 hc.1, ?_⟩), (hs.conj g c hgc).symm⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (g : Γ)⁻¹ * w * (g : Γ)⁻¹⁻¹ ∈ V₀ := S36E.conj_mem hV₀n (inv_mem g.2) hw
    have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hw'
    calc w * ((g : Γ) * c * (g : Γ)⁻¹) =
          g * (((g : Γ)⁻¹ * w * (g : Γ)⁻¹⁻¹) * c) * (g : Γ)⁻¹ := by group
      _ = g * (c * ((g : Γ)⁻¹ * w * (g : Γ)⁻¹⁻¹)) * (g : Γ)⁻¹ := by rw [h1]
      _ = ((g : Γ) * c * (g : Γ)⁻¹) * w := by group
  have hne : (Z.subgroupOf Vo).map p ≠ ⊥ := by
    intro hbot
    apply hpx
    have : p x ∈ (Z.subgroupOf Vo).map p :=
      ⟨x, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hx,
        Subgroup.mem_centralizer_iff.2 fun w hw => (hxc w hw).symm⟩), rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have htop := hirr _ hne hinv
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hmem : p ⟨v, hV₀ hv⟩ ∈ (Z.subgroupOf Vo).map p := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcv⟩ := hmem
  have hc : (c : Γ) ∈ Z := hc
  have hb : v * (c : Γ)⁻¹ ∈ V₀ ⊓ B :=
    Subgroup.mem_inf.2 ⟨mul_mem hv (inv_mem hc.1), ((hs.eq_iff ⟨v, hV₀ hv⟩ c).1 hcv.symm).2⟩
  have hwb : w * (v * (c : Γ)⁻¹) = (v * (c : Γ)⁻¹) * w := by
    have h1 := Subgroup.commutator_mem_commutator hw hb
    rwa [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have hwc : w * c = c * w := Subgroup.mem_centralizer_iff.1 hc.2 w hw
  have h := Commute.mul_right (hwb : Commute w (v * (c : Γ)⁻¹)) (hwc : Commute w c)
  rwa [inv_mul_cancel_right] at h

end Form

section Hat

variable {S : Type} [CommGroup S]

theorem sup_eq_top_of_hat {H : Subgroup (MulAut S)} (hH : S38H.HatMod H)
    {A : Subgroup (MulAut S)} (hAH : A ≤ H) (hf : Nat.card (fixV A) = 16) {c : MulAut S}
    (hc : c ∈ Subgroup.normalizer (H : Set (MulAut S)))
    (hne : (fixV A).map c.toMonoidHom ≠ fixV A) :
    fixV A ⊔ (fixV A).map c.toMonoidHom = ⊤ ∧ fixV A ⊓ (fixV A).map c.toMonoidHom ≠ ⊥ := by
  have := hH.finite
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have hAz : ∀ b ∈ A, b * zH = zH * b := fun b hb => S38H.HatMod.comm_z_of_mem hcen (hAH hb)
  have hcz : ∀ b ∈ A, b * (c⁻¹ * zH * c) = (c⁻¹ * zH * c) * b := by
    intro b hb
    have hb' : c * b * c⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hc b).1 (hAH hb)
    have h1 : c * b * c⁻¹ * zH = zH * (c * b * c⁻¹) := S38H.HatMod.comm_z_of_mem hcen hb'
    calc b * (c⁻¹ * zH * c) = c⁻¹ * (c * b * c⁻¹ * zH) * c := by group
      _ = c⁻¹ * (zH * (c * b * c⁻¹)) * c := by rw [h1]
      _ = (c⁻¹ * zH * c) * b := by group
  have hzW : ∀ s ∈ fixV A, (zH : MulAut S) s ∈ fixV A := fun s hs =>
    S38H.HatMod.z_mem_fixV hAz hs
  have hzW' : ∀ s ∈ (fixV A).map c.toMonoidHom,
      (zH : MulAut S) s ∈ (fixV A).map c.toMonoidHom := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨(c⁻¹ * zH * c) s, S38H.HatMod.z_mem_fixV hcz hs, ?_⟩
    show c ((c⁻¹ * zH * c) s) = (zH : MulAut S) (c s)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  have hcW' : Nat.card ((fixV A).map c.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective c.injective, hf]
  have hS : Nat.card S = 64 := by rw [hH.card]; norm_num
  have hsup : ∀ s ∈ fixV A ⊔ (fixV A).map c.toMonoidHom,
      (zH : MulAut S) s ∈ fixV A ⊔ (fixV A).map c.toMonoidHom := by
    have hle : fixV A ⊔ (fixV A).map c.toMonoidHom ≤
        (fixV A ⊔ (fixV A).map c.toMonoidHom).comap (zH : MulAut S).toMonoidHom :=
      sup_le (fun s hs => Subgroup.mem_sup_left (hzW s hs))
        (fun s hs => Subgroup.mem_sup_right (hzW' s hs))
    exact fun s hs => hle hs
  have hWle : fixV A ≤ fixV A ⊔ (fixV A).map c.toMonoidHom := le_sup_left
  have h16 : 16 ≤ Nat.card ↥(fixV A ⊔ (fixV A).map c.toMonoidHom) :=
    hf ▸ Subgroup.card_le_of_le hWle
  refine ⟨?_, ?_⟩
  · rcases HatA6.card_cases_of_inv hH.card h3 hfp hsup with h | h | h | h
    · omega
    · omega
    · exfalso
      apply hne
      have hWeq : fixV A = fixV A ⊔ (fixV A).map c.toMonoidHom :=
        Subgroup.eq_of_le_of_card_ge hWle (by rw [h, hf])
      exact Subgroup.eq_of_le_of_card_ge (le_sup_right.trans hWeq.ge) (by rw [hf, hcW'])
    · exact Subgroup.eq_top_of_card_eq _ (h.trans hS.symm)
  · intro hbot
    have hidx : (fixV A ⊓ (fixV A).map c.toMonoidHom).index ≤
        (fixV A).index * ((fixV A).map c.toMonoidHom).index := Subgroup.index_inf_le
    have hiW : (fixV A).index = 4 := by
      have := (fixV A).card_mul_index
      rw [hf, hS] at this
      omega
    have hiW' : ((fixV A).map c.toMonoidHom).index = 4 := by
      have := ((fixV A).map c.toMonoidHom).card_mul_index
      rw [hcW', hS] at this
      omega
    rw [hbot, Subgroup.index_bot, hS, hiW, hiW'] at hidx
    omega

end Hat

section Form

variable {Γ : Type} [Group Γ] {Ga Vo B V₀ : Subgroup Γ} {S : Type} [CommGroup S]
  {p : ↥Vo →* S} {ρ : ↥Ga →* MulAut S}

theorem commutator_eq_bot_of_hat (hs : S36E.SecData Ga Vo (Vo ⊓ B) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤) (hV₀ : V₀ ≤ Vo)
    (hV₀G : V₀ ≤ Ga) (hV₀n : Ga ≤ Subgroup.normalizer (V₀ : Set Γ)) (hV₀B : ¬ V₀ ≤ B)
    (hcomm : ⁅V₀, V₀ ⊓ B⁆ = ⊥) (hcen : ∀ v ∈ V₀, ∀ w ∈ V₀, ∀ g ∈ Ga, g * ⁅v, w⁆ = ⁅v, w⁆ * g)
    {H : Subgroup (MulAut S)} (hH : S38H.HatMod H)
    (hXH : ρ.range ≤ Subgroup.normalizer (H : Set (MulAut S))) {A : Subgroup (MulAut S)}
    (hAX : A ≤ ρ.range) (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card S ≤ Nat.card A * Nat.card (fixV A)) : ⁅V₀, V₀⁆ = ⊥ := by
  have := hH.finite
  have hsurj := exists_mem_of_irr hs hirr hV₀ hV₀n hV₀B
  obtain ⟨hAH, -, hf, hfc⟩ := hH.offender (hAX.trans hXH) hA hA1 hoff
  have hS : Nat.card S = 64 := by rw [hH.card]; norm_num
  obtain ⟨g, hg⟩ : ∃ g : ↥Ga, (fixV A).map (ρ g).toMonoidHom ≠ fixV A := by
    by_contra hcon
    push Not at hcon
    have hinv : S512N.IsInv ρ (fixV A) := fun g s hs' => by
      rw [← hcon g]
      exact ⟨s, hs', rfl⟩
    have hne : fixV A ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hf
      omega
    rw [hirr _ hne hinv, Subgroup.card_top, hS] at hf
    omega
  obtain ⟨htop, hint⟩ := sup_eq_top_of_hat hH hAH hf (hXH ⟨g, rfl⟩) hg
  obtain ⟨⟨s, hsW, hsW'⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hint
  obtain ⟨x, hxV, hxs⟩ := hsurj s
  refine commutator_eq_bot_of_commute hs hirr hV₀ hV₀n hcomm hxV ?_ fun w hw => ?_
  · rw [hxs]
    exact fun h1 => hs1 (Subtype.ext h1)
  · have hpw : p ⟨w, hV₀ hw⟩ ∈ fixV A ⊔ (fixV A).map (ρ g).toMonoidHom := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨s₁, hs₁, s₂, hs₂, hs₁₂⟩ := Subgroup.mem_sup.1 hpw
    obtain ⟨w₁, hw₁, rfl⟩ := hsurj s₁
    obtain ⟨w₂, hw₂, rfl⟩ := hsurj s₂
    have h1 : (x : Γ) * w₁ = w₁ * x :=
      commute_of_mem_fixV hs hV₀G hV₀n hcomm hcen hsurj hAX hxV hw₁ (by rw [hxs]; exact hsW)
        (hfc hs₁)
    have h2 : (x : Γ) * w₂ = w₂ * x :=
      commute_of_mem_map_fixV hs hV₀G hV₀n hcomm hcen hsurj hAX g hxV hw₂
        (by rw [hxs]; exact hsW') (Subgroup.map_mono hfc hs₂)
    have hb : w * ((w₁ : Γ) * w₂)⁻¹ ∈ V₀ ⊓ B := Subgroup.mem_inf.2
      ⟨mul_mem hw (inv_mem (mul_mem hw₁ hw₂)),
        ((hs.eq_iff ⟨w, hV₀ hw⟩ (w₁ * w₂)).1 (by rw [map_mul]; exact hs₁₂.symm)).2⟩
    have h3 : (x : Γ) * (w * ((w₁ : Γ) * w₂)⁻¹) = (w * ((w₁ : Γ) * w₂)⁻¹) * x := by
      have h := Subgroup.commutator_mem_commutator hxV hb
      rwa [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    have h := Commute.mul_right (h3 : Commute (x : Γ) (w * ((w₁ : Γ) * w₂)⁻¹))
      (Commute.mul_right (h1 : Commute (x : Γ) w₁) (h2 : Commute (x : Γ) w₂))
    rwa [inv_mul_cancel_right] at h

end Form

end S512L

end CFSG.Quasithin.MS93
