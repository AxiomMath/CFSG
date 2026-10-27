module

public import CFSG.Quasithin.Vol2.Ch3xC58NSA5Mate
public import CFSG.Quasithin.Vol2.Ch3xC58NSGood
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 CFSG.Quasithin.C58
  CFSG.QuasithinUnique.AppC CFSG.QuasithinUnique.A5.Delta5 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem four_cases : ∀ a ∈ Eset, ∀ b ∈ Eset, ∀ d ∈ Dset, d ∉ Eset →
    (∀ g ∈ four a b, d * g * d⁻¹ ∈ four a b) →
      four a b = {1} ∨ four a b = Eset ∨ (four a b).card * (fixOf a b).card < 16 := by
  decide +kernel

theorem fix_prod : ∀ w : Fin 5 → ZMod 2, isEven w → pact (swap 0 1 * swap 2 3) w = w →
    pact (swap 0 1) w = w ∧ pact (swap 2 3) w = w := by
  decide +kernel

namespace A5Cfg

variable {L R S : Subgroup G} {P : A5Pi L} (hc : A5Cfg L R S P)
include hc

theorem mem_normalizer_of_sqSub {x : G} (hxS : x ∈ normalizer (S : Set G))
    (hxR : x ∈ normalizer (R : Set G))
    (hxU : ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G)) {g : G} (hgR : g ∈ R)
    (hgF : g ∈ normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G)) :
    g ∈ normalizer (L : Set G) := by
  by_contra hg
  set D := S ⊓ centralizer (L : Set G) with hDdef
  have hVE := hc.im_V_eq hxS hxR hxU
  have hg'N : g⁻¹ ∉ normalizer (L : Set G) := fun h => hg (by simpa using inv_mem h)
  have hperm := hc.perm g⁻¹ (inv_mem hgR) hg'N
  have hgS : g ∈ normalizer (S : Set G) := hc.RS hgR
  set U₂ := conjSubgroup (blockU L) g⁻¹ with hU₂
  have hU₂S : U₂ ≤ S := by
    have := conjSubgroup_mono hc.US g⁻¹
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (inv_mem hgS)] at this
  have hU₂C : ∀ w ∈ U₂, ∀ a ∈ L, a * w = w * a := fun w hw a ha =>
    hperm a ha w (conjSubgroup_mono hc.U_le_L g⁻¹ hw)
  have hU₂D : U₂ ≤ D := fun w hw => ⟨hU₂S hw, mem_centralizer_iff.mpr fun a ha => hU₂C w hw a ha⟩
  obtain ⟨d, hdD, w, hwU₂, hdw⟩ : ∃ d ∈ D, ∃ w ∈ U₂, d * w * d⁻¹ * w⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hDC : ∀ d ∈ D, ∀ w ∈ U₂, d * w = w * d := fun d hd w hw =>
      mul_inv_eq_one.mp (by simpa [mul_assoc] using hall d hd w hw)
    have hSC : S ≤ centralizer (U₂ : Set G) := by
      rw [← hc.sup_V_Q hxS hVE, hc.QD]
      refine sup_le ?_ (sup_le ?_ ?_)
      · intro v hv
        rw [mem_centralizer_iff]
        intro w hw
        exact (mem_centralizer_iff.mp (hc.D_le_centralizer_V hxS hVE (hU₂D hw)) v hv).symm
      · intro u hu
        rw [mem_centralizer_iff]
        intro w hw
        exact (hU₂C w hw u (hc.U_le_L hu)).symm
      · intro e he
        rw [mem_centralizer_iff]
        intro w hw
        exact (hDC e he w hw).symm
    have hSU : S ≤ centralizer (blockU L : Set G) := by
      have h1 := conjSubgroup_mono hSC g
      rw [conjSubgroup_eq_iff_mem_normalizer.mpr hgS, conjSubgroup_centralizer, hU₂,
        conjSubgroup_inv_conjSubgroup] at h1
      exact h1
    have hσ : swap (0 : Fin 5) 1 ∈ P.im S := by rw [hc.SE]; exact (mem_Estd _).2 t1_mem_Eset
    obtain ⟨s, hs, hsσ⟩ := (P.mem_im_pf hc.SN).1 hσ
    have := pf_eq_one (P := P) (hc.SN hs) (hSU hs)
    rw [hsσ] at this
    exact absurd this (by decide +kernel)
  have hwF : d * w * d⁻¹ * w⁻¹ ∈ sqSub D := commutator_mem_sqSub hdD (hU₂D hwU₂)
  have hwU : d * w * d⁻¹ * w⁻¹ ∈ U₂ := by
    have hdN : d ∈ normalizer ((U₂ : Subgroup G) : Set G) := by
      have := conjSubgroup_mono hc.S_le_NU g⁻¹
      rw [conjSubgroup_eq_iff_mem_normalizer.mpr (inv_mem hgS), conjSubgroup_normalizer] at this
      exact this hdD.1
    exact mul_mem ((mem_normalizer_iff.mp hdN w).mp hwU₂) (inv_mem hwU₂)
  have h1 : g⁻¹ * (d * w * d⁻¹ * w⁻¹) * g ∈ blockU L := by
    have := mem_conjSubgroup_iff.mp hwU
    simpa using this
  have h2 : g⁻¹ * (d * w * d⁻¹ * w⁻¹) * g ∈ sqSub D := by
    have := (mem_normalizer_iff.mp (inv_mem hgF) _).mp hwF
    simpa using this
  have h3 := hc.eq_one_of_mem h1 (sqSub_le_self h2).2
  apply hdw
  calc d * w * d⁻¹ * w⁻¹ = g * (g⁻¹ * (d * w * d⁻¹ * w⁻¹) * g) * g⁻¹ := by group
    _ = 1 := by rw [h3]; group

theorem comm_S_D {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : P.im (conjSubgroup (blockU L) x) = Estd) {b d : G} (hb : b ∈ S)
    (hd : d ∈ S ⊓ centralizer (L : Set G)) :
    b * d * b⁻¹ * d⁻¹ ∈ sqSub (S ⊓ centralizer (L : Set G)) := by
  obtain ⟨u', hu', hq⟩ := hc.exists_mem_V_mul_Q hx hVE hb
  rw [hc.QD] at hq
  obtain ⟨u, hu, d', hd', hud⟩ := mem_sup_of_commute (fun u hu d hd => hc.DU hu hd) hq
  have hb' : b = u' * (u * d') := by rw [← hud]; group
  have hc1 : d' * d * d'⁻¹ ∈ S ⊓ centralizer (L : Set G) := mul_mem (mul_mem hd' hd) (inv_mem hd')
  have e1 : u * (d' * d * d'⁻¹) = (d' * d * d'⁻¹) * u := hc.DU hu hc1
  have e2 : u' * (d' * d * d'⁻¹) = (d' * d * d'⁻¹) * u' :=
    mem_centralizer_iff.mp (hc.D_le_centralizer_V hx hVE hc1) u' hu'
  have e : u' * (u * d') * d * (u' * (u * d'))⁻¹ * d⁻¹ = d' * d * d'⁻¹ * d⁻¹ := by
    calc u' * (u * d') * d * (u' * (u * d'))⁻¹ * d⁻¹
        = u' * (u * (d' * d * d'⁻¹)) * u⁻¹ * u'⁻¹ * d⁻¹ := by group
      _ = u' * ((d' * d * d'⁻¹) * u) * u⁻¹ * u'⁻¹ * d⁻¹ := by rw [e1]
      _ = (u' * (d' * d * d'⁻¹)) * u'⁻¹ * d⁻¹ := by group
      _ = ((d' * d * d'⁻¹) * u') * u'⁻¹ * d⁻¹ := by rw [e2]
      _ = d' * d * d'⁻¹ * d⁻¹ := by group
  rw [hb', e]
  exact commutator_mem_sqSub hd' hd

omit [Finite G] in
theorem modElem_Q :
    ModElem S (sqSub (S ⊓ centralizer (L : Set G))) (S ⊓ centralizer (blockU L : Set G)) := by
  refine ⟨inf_le_left, fun q hq => ?_, fun q hq q' hq' => ?_⟩
  · rw [hc.QD] at hq
    obtain ⟨u, hu, d, hd, rfl⟩ := mem_sup_of_commute (fun u hu d hd => hc.DU hu hd) hq
    have hcd : u * d = d * u := hc.DU hu hd
    have e : (u * d) ^ 2 = u ^ 2 * d ^ 2 := by
      calc (u * d) ^ 2 = u * (d * u) * d := by simp [pow_two, mul_assoc]
        _ = u * (u * d) * d := by rw [← hcd]
        _ = u ^ 2 * d ^ 2 := by simp [pow_two, mul_assoc]
    rw [e, hc.U_sq hu, one_mul]
    exact sq_mem_sqSub hd
  · rw [hc.QD] at hq hq'
    obtain ⟨u, hu, d, hd, rfl⟩ := mem_sup_of_commute (fun u hu d hd => hc.DU hu hd) hq
    obtain ⟨u', hu', d', hd', rfl⟩ := mem_sup_of_commute (fun u hu d hd => hc.DU hu hd) hq'
    have huu : u * u' = u' * u := hc.U_comm hu hu'
    have c1 : ∀ v ∈ blockU L, ∀ e ∈ S ⊓ centralizer (L : Set G), v * e = e * v :=
      fun v hv e he => hc.DU hv he
    have e : u * d * (u' * d') * (u * d)⁻¹ * (u' * d')⁻¹ =
        (u * u' * u⁻¹ * u'⁻¹) * (d * d' * d⁻¹ * d'⁻¹) := by
      have k1 := c1 u' hu' d hd
      have k2' := c1 u⁻¹ (inv_mem hu) d' hd'
      have k4' := c1 u⁻¹ (inv_mem hu) d hd
      have k8 := c1 u⁻¹ (inv_mem hu) d⁻¹ (inv_mem hd)
      calc u * d * (u' * d') * (u * d)⁻¹ * (u' * d')⁻¹
          = u * (d * u') * d' * d⁻¹ * u⁻¹ * d'⁻¹ * u'⁻¹ := by group
        _ = u * (u' * d) * d' * d⁻¹ * u⁻¹ * d'⁻¹ * u'⁻¹ := by rw [k1]
        _ = u * u' * d * d' * (d⁻¹ * u⁻¹) * d'⁻¹ * u'⁻¹ := by group
        _ = u * u' * d * d' * (u⁻¹ * d⁻¹) * d'⁻¹ * u'⁻¹ := by rw [k8]
        _ = u * u' * d * (d' * u⁻¹) * d⁻¹ * d'⁻¹ * u'⁻¹ := by group
        _ = u * u' * d * (u⁻¹ * d') * d⁻¹ * d'⁻¹ * u'⁻¹ := by rw [k2']
        _ = u * u' * (d * u⁻¹) * d' * d⁻¹ * d'⁻¹ * u'⁻¹ := by group
        _ = u * u' * (u⁻¹ * d) * d' * d⁻¹ * d'⁻¹ * u'⁻¹ := by rw [k4']
        _ = u * u' * u⁻¹ * (d * d' * d⁻¹ * d'⁻¹) * u'⁻¹ := by group
        _ = u * u' * u⁻¹ * u'⁻¹ * (d * d' * d⁻¹ * d'⁻¹) := by
            have hm : d * d' * d⁻¹ * d'⁻¹ ∈ S ⊓ centralizer (L : Set G) :=
              mul_mem (mul_mem (mul_mem hd hd') (inv_mem hd)) (inv_mem hd')
            have := c1 u'⁻¹ (inv_mem hu') _ hm
            rw [mul_assoc (u * u' * u⁻¹), ← this, ← mul_assoc]
    rw [e]
    have e2 : u * u' * u⁻¹ * u'⁻¹ = 1 := by rw [huu]; group
    rw [e2, one_mul]
    exact commutator_mem_sqSub hd hd'

theorem mem_Q_of_comm {z : G} (hzS : z ∈ S)
    (hz : ∀ b ∈ S, z * b * z⁻¹ * b⁻¹ ∈ sqSub (S ⊓ centralizer (L : Set G))) :
    z ∈ S ⊓ centralizer (blockU L : Set G) := by
  refine ⟨hzS, mem_centralizer_iff.mpr fun u hu => ?_⟩
  have h1 := hz u (hc.US hu)
  have h2 : z * u * z⁻¹ * u⁻¹ ∈ blockU L :=
    mul_mem (PiData.conj_mem_U (hc.SN hzS) hu) (inv_mem hu)
  have h3 := hc.eq_one_of_mem h2 (sqSub_le_self h1).2
  have h4 : z * u * z⁻¹ = u := mul_inv_eq_one.mp h3
  exact (mul_inv_eq_iff_eq_mul.mp h4).symm

theorem conj_D_le {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : P.im (conjSubgroup (blockU L) x) = Estd) {g : G} (hgS : g ∈ normalizer (S : Set G))
    (hgF : g ∈ normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G)) :
    conjSubgroup (S ⊓ centralizer (L : Set G)) g ≤ S ⊓ centralizer (blockU L : Set G) := by
  intro e he
  have heD : g * e * g⁻¹ ∈ S ⊓ centralizer (L : Set G) := mem_conjSubgroup_iff.mp he
  have heS : e ∈ S := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hgS) _).mp heD.1
    have e1 : g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e := by group
    rwa [e1] at h1
  refine hc.mem_Q_of_comm heS fun b hb => ?_
  have hb' : g * b * g⁻¹ ∈ S := (mem_normalizer_iff.mp hgS b).mp hb
  have h1 := hc.comm_S_D hx hVE hb' heD
  have h2 : g * e * g⁻¹ * (g * b * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ ∈
      sqSub (S ⊓ centralizer (L : Set G)) := by
    have := inv_mem h1
    have e2 : (g * b * g⁻¹ * (g * e * g⁻¹) * (g * b * g⁻¹)⁻¹ * (g * e * g⁻¹)⁻¹)⁻¹ =
        g * e * g⁻¹ * (g * b * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
    rwa [e2] at this
  have h3 := (mem_normalizer_iff.mp (inv_mem hgF) _).mp h2
  have e3 : g⁻¹ * (g * e * g⁻¹ * (g * b * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹) * g⁻¹⁻¹ =
      e * b * e⁻¹ * b⁻¹ := by group
  rwa [e3] at h3

theorem exists_decomp {x : G} (hx : x ∈ normalizer (S : Set G))
    (hVE : P.im (conjSubgroup (blockU L) x) = Estd) {a : G} (ha : a ∈ S) :
    ∃ v ∈ conjSubgroup (blockU L) x, ∃ u ∈ blockU L, ∃ d ∈ S ⊓ centralizer (L : Set G),
      a = v * u * d ∧ P.pf v = P.pf a := by
  obtain ⟨v, hv, hq⟩ := hc.exists_mem_V_mul_Q hx hVE ha
  have hq' := hq
  rw [hc.QD] at hq'
  obtain ⟨u, hu, d, hd, hud⟩ := mem_sup_of_commute (fun u hu d hd => hc.DU hu hd) hq'
  refine ⟨v, hv, u, hu, d, hd, ?_, ?_⟩
  · calc a = v * (v⁻¹ * a) := by group
      _ = v * (u * d) := by rw [hud]
      _ = v * u * d := by group
  · have hvN := hc.V_le_N hx hv
    have hqN : v⁻¹ * a ∈ normalizer (L : Set G) := hc.SN hq.1
    have h1 : P.pf (v⁻¹ * a) = 1 := pf_eq_one hqN hq.2
    calc P.pf v = P.pf v * P.pf (v⁻¹ * a) := by rw [h1, mul_one]
      _ = P.pf (v * (v⁻¹ * a)) := (P.pf_mul hvN hqN).symm
      _ = P.pf a := by rw [mul_inv_cancel_left]

theorem eq_of_modElem {x : G} (hxS : x ∈ normalizer (S : Set G))
    (hVE : P.im (conjSubgroup (blockU L) x) = Estd) {A : Subgroup G}
    (hA : ModElem S (sqSub (S ⊓ centralizer (L : Set G))) A)
    (hcard : Nat.card ↥(S ⊓ centralizer (blockU L : Set G)) ≤ Nat.card A) {r : G}
    (hrN : r ∈ normalizer (L : Set G)) (hrA : r ∈ normalizer (A : Set G))
    (hrD : P.pf r ∈ Dset) (hrE : P.pf r ∉ Eset) :
    A = S ⊓ centralizer (blockU L : Set G) ∨
      A = conjSubgroup (blockU L) x ⊔ (S ⊓ centralizer (L : Set G)) := by
  classical
  set D := S ⊓ centralizer (L : Set G) with hDdef
  set F := sqSub D with hFdef
  have hAS : A ≤ S := hA.1
  have hAN : A ≤ normalizer (L : Set G) := hAS.trans hc.SN
  have hFD : F ≤ D := sqSub_le_self
  have hpfD : ∀ d ∈ D, P.pf d = 1 := fun d hd => pf_eq_one (hc.SN hd.1) (hc.D_le_Q hd).2
  have hsq : ∀ g ∈ P.im A, g * g = 1 := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := (P.mem_im_pf hAN).1 hg
    rw [← P.pf_mul (hAN ha) (hAN ha), ← pow_two]
    exact hpfD _ (hFD (hA.2.1 a ha))
  have hcm : ∀ g ∈ P.im A, ∀ h ∈ P.im A, g * h = h * g := by
    intro g hg h hh
    obtain ⟨a, ha, rfl⟩ := (P.mem_im_pf hAN).1 hg
    obtain ⟨b, hb, rfl⟩ := (P.mem_im_pf hAN).1 hh
    have hc' := hA.2.2 a ha b hb
    have e : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    have hcN : a * b * a⁻¹ * b⁻¹ ∈ normalizer (L : Set G) := hc.SN (hFD hc').1
    calc P.pf a * P.pf b = P.pf (a * b) := (P.pf_mul (hAN ha) (hAN hb)).symm
      _ = P.pf ((a * b * a⁻¹ * b⁻¹) * (b * a)) := by rw [← e]
      _ = P.pf (a * b * a⁻¹ * b⁻¹) * P.pf (b * a) :=
          P.pf_mul hcN (mul_mem (hAN hb) (hAN ha))
      _ = P.pf (b * a) := by rw [hpfD _ (hFD hc'), one_mul]
      _ = P.pf b * P.pf a := P.pf_mul (hAN hb) (hAN ha)
  obtain ⟨a₀, ha₀, b₀, hb₀, hab, hcP, hfix⟩ := exists_four_card (P.im A) hsq hcm
  have hAle : P.im A ≤ Estd := by rw [← hc.SE]; exact P.im_mono hAS
  have hAE : ∀ g ∈ P.im A, g ∈ Eset := fun g hg => (mem_Estd g).1 (hAle hg)
  have hnorm : ∀ g ∈ four a₀ b₀, P.pf r * g * (P.pf r)⁻¹ ∈ four a₀ b₀ := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := (P.mem_im_pf hAN).1 ((hab g).2 hg)
    have ha' : r * a * r⁻¹ ∈ A := (mem_normalizer_iff.mp hrA a).mp ha
    refine (hab _).1 ((P.mem_im_pf hAN).2 ⟨_, ha', ?_⟩)
    rw [P.pf_mul (mul_mem hrN (hAN ha)) (inv_mem hrN), P.pf_mul hrN (hAN ha), P.pf_inv hrN]
  have hU_D : ∀ u ∈ blockU L, ∀ d ∈ D, u * d = d * u := fun u hu d hd => hc.DU hu hd
  have hcardQ : Nat.card ↥(S ⊓ centralizer (blockU L : Set G)) = 16 * Nat.card D := by
    have hN : blockU L ≤ normalizer (D : Set G) := le_normalizer_of_commute hU_D
    have h1 := card_sup_mul_card_inf_of_le_normalizer hN
    have hbot : blockU L ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      exact hc.eq_one_of_mem hw.1 hw.2.2
    rw [hbot, Subgroup.card_bot, mul_one, ← hc.QD, P.card_blockU] at h1
    exact h1
  have hinf : A ⊓ centralizer (blockU L : Set G) ≤
      (blockU L ⊓ centralizer (A : Set G)) ⊔ D := by
    intro q hq
    have hqQ : q ∈ S ⊓ centralizer (blockU L : Set G) := ⟨hAS hq.1, hq.2⟩
    rw [hc.QD] at hqQ
    obtain ⟨u, hu, d, hd, rfl⟩ := mem_sup_of_commute hU_D hqQ
    refine mul_mem (mem_sup_left ⟨hu, mem_centralizer_iff.mpr fun a ha => ?_⟩) (mem_sup_right hd)
    have hcomm := hA.2.2 a ha (u * d) hq.1
    set e := a * d * a⁻¹ * d⁻¹ with he
    have heF : e ∈ F := hc.comm_S_D hxS hVE (hAS ha) hd
    have heD : e ∈ D := hFD heF
    have hue : u * e = e * u := hU_D u hu e heD
    have key : a * (u * d) * a⁻¹ * (u * d)⁻¹ = (a * u * a⁻¹ * u⁻¹) * (u * e * u⁻¹) := by
      rw [he]; group
    have hue' : u * e * u⁻¹ = e := by rw [hue]; group
    rw [key, hue'] at hcomm
    have hcF : a * u * a⁻¹ * u⁻¹ ∈ F := by
      have := mul_mem hcomm (inv_mem heF)
      simpa [mul_assoc] using this
    have hcU : a * u * a⁻¹ * u⁻¹ ∈ blockU L :=
      mul_mem (PiData.conj_mem_U (hAN ha) hu) (inv_mem hu)
    have h1 := hc.eq_one_of_mem hcU (hFD hcF).2
    have h2 : a * u * a⁻¹ = u := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hbound : Nat.card A ≤ Nat.card (P.im A) * Nat.card (FixΔ (P.im A)) * Nat.card D := by
    have h1 := P.card_im_mul hAN
    have h2 : Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) ≤
        Nat.card ↥((blockU L ⊓ centralizer (A : Set G)) ⊔ D) := Subgroup.card_le_of_le hinf
    have hN : blockU L ⊓ centralizer (A : Set G) ≤ normalizer (D : Set G) :=
      le_normalizer_of_commute fun u hu d hd => hU_D u hu.1 d hd
    have h3 := card_sup_mul_card_inf_of_le_normalizer hN
    have h4 := P.card_fix hAN
    have hpos : 0 < Nat.card ↥((blockU L ⊓ centralizer (A : Set G)) ⊓ D) := Nat.card_pos
    have h5 : Nat.card ↥((blockU L ⊓ centralizer (A : Set G)) ⊔ D) ≤
        Nat.card ↥(blockU L ⊓ centralizer (A : Set G)) * Nat.card D := by
      rw [← h3]; exact Nat.le_mul_of_pos_right _ hpos
    rw [h4] at h5
    calc Nat.card A = Nat.card (P.im A) * Nat.card ↥(A ⊓ centralizer (blockU L : Set G)) := h1.symm
      _ ≤ Nat.card (P.im A) * (Nat.card (FixΔ (P.im A)) * Nat.card D) :=
          Nat.mul_le_mul_left _ (h2.trans h5)
      _ = _ := by ring
  rcases four_cases a₀ (hAE a₀ ha₀) b₀ (hAE b₀ hb₀) (P.pf r) hrD hrE hnorm with h1 | h1 | h1
  ·
    left
    have hle : A ≤ S ⊓ centralizer (blockU L : Set G) := by
      intro a ha
      refine ⟨hAS ha, mem_centralizer_of_pf (P := P) (hAN ha) ?_⟩
      have := (hab (P.pf a)).1 ((P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩)
      rw [h1] at this
      exact Finset.mem_singleton.1 this
    exact Subgroup.eq_of_le_of_card_ge hle hcard
  ·
    right
    set V := conjSubgroup (blockU L) x with hVdef
    have hmemE : ∀ σ ∈ Eset, ∃ a ∈ A, P.pf a = σ := fun σ hσ =>
      (P.mem_im_pf hAN).1 ((hab σ).2 (by rw [h1]; exact hσ))
    obtain ⟨a₁, ha₁, hpa₁⟩ := hmemE _ t1_mem_Eset
    obtain ⟨a₂, ha₂, hpa₂⟩ := hmemE _ t2_mem_Eset
    obtain ⟨v₁, hv₁, u₁, hu₁, d₁, hd₁, rfl, hpv₁⟩ := hc.exists_decomp hxS hVE (hAS ha₁)
    obtain ⟨v₂, hv₂, u₂, hu₂, d₂, hd₂, rfl, hpv₂⟩ := hc.exists_decomp hxS hVE (hAS ha₂)
    have hVD : ∀ v ∈ V, ∀ d ∈ D, v * d = d * v := fun v hv d hd =>
      mem_centralizer_iff.mp (hc.D_le_centralizer_V hxS hVE hd) v hv
    have hvinv : ∀ v ∈ V, v⁻¹ = v := fun v hv =>
      inv_eq_of_mul_eq_one_right (by
        have := ((C1.elemAb2_blockU hc.short).conjSubgroup x).2 v hv
        simpa [pow_two] using this)
    have hsq_vu : ∀ v ∈ V, ∀ u ∈ blockU L, ∀ d ∈ D, v * u * d ∈ A → v * u = u * v := by
      intro v hv u hu d hd ha
      have h2 := hA.2.1 _ ha
      have hdvu : d * (v * u) = (v * u) * d := by
        rw [← mul_assoc, ← hVD v hv d hd, mul_assoc, ← hU_D u hu d hd, ← mul_assoc]
      have e : (v * u * d) ^ 2 = (v * u) ^ 2 * d ^ 2 := by
        calc (v * u * d) ^ 2 = (v * u) * (d * (v * u)) * d := by simp [pow_two, mul_assoc]
          _ = (v * u) * ((v * u) * d) * d := by rw [hdvu]
          _ = (v * u) ^ 2 * d ^ 2 := by simp [pow_two, mul_assoc]
      rw [e] at h2
      have hF2 : (v * u) ^ 2 ∈ F := by
        have := mul_mem h2 (inv_mem (sq_mem_sqSub hd))
        simpa [mul_assoc] using this
      have hU2 : (v * u) ^ 2 ∈ blockU L := by
        have e2 : (v * u) ^ 2 = (v * u * v⁻¹) * u := by rw [pow_two, hvinv v hv]; group
        rw [e2]
        exact mul_mem (PiData.conj_mem_U (hc.V_le_N hxS hv) hu) hu
      have h3 := hc.eq_one_of_mem hU2 (hFD hF2).2
      have h4 : v * u * v * u = 1 := by rw [← h3]; simp [pow_two, mul_assoc]
      calc v * u = (v * u * v * u) * u⁻¹ * v⁻¹ := by group
        _ = u * v := by rw [h4, one_mul, hc.U_inv hu, hvinv v hv]
    have hcomm_vu : ∀ v ∈ V, ∀ u ∈ blockU L, ∀ d ∈ D, v * u * d ∈ A →
        ∀ v' ∈ V, ∀ u' ∈ blockU L, ∀ d' ∈ D, v' * u' * d' ∈ A →
          (v * u) * (v' * u') = (v' * u') * (v * u) := by
      intro v hv u hu d hd ha v' hv' u' hu' d' hd' ha'
      have hcomm := hA.2.2 _ ha _ ha'
      set X := v * u with hX
      set Y := v' * u' with hY
      have hdX : d * X = X * d := by
        rw [hX, ← mul_assoc, ← hVD v hv d hd, mul_assoc, ← hU_D u hu d hd, ← mul_assoc]
      have hdY : d * Y = Y * d := by
        rw [hY, ← mul_assoc, ← hVD v' hv' d hd, mul_assoc, ← hU_D u' hu' d hd, ← mul_assoc]
      have hd'X : d' * X = X * d' := by
        rw [hX, ← mul_assoc, ← hVD v hv d' hd', mul_assoc, ← hU_D u hu d' hd', ← mul_assoc]
      have hcD : d * d' * d⁻¹ * d'⁻¹ ∈ D :=
        mul_mem (mul_mem (mul_mem hd hd') (inv_mem hd)) (inv_mem hd')
      have hcYX : (d * d' * d⁻¹ * d'⁻¹) * (Y * X) = (Y * X) * (d * d' * d⁻¹ * d'⁻¹) := by
        have h1 : (d * d' * d⁻¹ * d'⁻¹) * Y = Y * (d * d' * d⁻¹ * d'⁻¹) := by
          rw [hY, ← mul_assoc, ← hVD v' hv' _ hcD, mul_assoc, ← hU_D u' hu' _ hcD,
            ← mul_assoc]
        have h2 : (d * d' * d⁻¹ * d'⁻¹) * X = X * (d * d' * d⁻¹ * d'⁻¹) := by
          rw [hX, ← mul_assoc, ← hVD v hv _ hcD, mul_assoc, ← hU_D u hu _ hcD, ← mul_assoc]
        rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
      have hab' : X * d * (Y * d') = X * Y * (d * d') := by
        rw [mul_assoc X d, ← mul_assoc d Y d', hdY]; group
      have hba' : Y * d' * (X * d) = Y * X * (d' * d) := by
        rw [mul_assoc Y d', ← mul_assoc d' X d, hd'X]; group
      have hinvc : (d * d' * d⁻¹ * d'⁻¹) * (Y * X)⁻¹ = (Y * X)⁻¹ * (d * d' * d⁻¹ * d'⁻¹) :=
        (show Commute (d * d' * d⁻¹ * d'⁻¹) (Y * X) from hcYX).inv_right.eq
      have key : (X * d) * (Y * d') * (X * d)⁻¹ * (Y * d')⁻¹ =
          (X * Y * X⁻¹ * Y⁻¹) * (d * d' * d⁻¹ * d'⁻¹) := by
        calc (X * d) * (Y * d') * (X * d)⁻¹ * (Y * d')⁻¹ =
              ((X * d) * (Y * d')) * ((Y * d') * (X * d))⁻¹ := by group
          _ = (X * Y * (d * d')) * (Y * X * (d' * d))⁻¹ := by rw [hab', hba']
          _ = X * Y * ((d * d' * d⁻¹ * d'⁻¹) * (Y * X)⁻¹) := by group
          _ = X * Y * ((Y * X)⁻¹ * (d * d' * d⁻¹ * d'⁻¹)) := by rw [hinvc]
          _ = (X * Y * X⁻¹ * Y⁻¹) * (d * d' * d⁻¹ * d'⁻¹) := by group
      have hXd : v * u * d = X * d := by rw [hX]
      have hYd : v' * u' * d' = Y * d' := by rw [hY]
      rw [hXd, hYd, key] at hcomm
      have hF1 : X * Y * X⁻¹ * Y⁻¹ ∈ F := by
        have := mul_mem hcomm (inv_mem (commutator_mem_sqSub hd hd'))
        simpa [mul_assoc] using this
      have hvv : v * v' = v' * v := hc.V_comm hv hv'
      have hm₁ : v'⁻¹ * u * v' * u' ∈ blockU L :=
        mul_mem (by simpa using PiData.conj_mem_U (inv_mem (hc.V_le_N hxS hv')) hu) hu'
      have hm₂ : v⁻¹ * u' * v * u ∈ blockU L :=
        mul_mem (by simpa using PiData.conj_mem_U (inv_mem (hc.V_le_N hxS hv)) hu') hu
      have hU1 : X * Y * X⁻¹ * Y⁻¹ ∈ blockU L := by
        have e : X * Y * X⁻¹ * Y⁻¹ =
            (v * v') * ((v'⁻¹ * u * v' * u') * (v⁻¹ * u' * v * u)⁻¹) * (v' * v)⁻¹ := by
          rw [hX, hY]; group
        rw [e, ← hvv]
        exact PiData.conj_mem_U (mul_mem (hc.V_le_N hxS hv) (hc.V_le_N hxS hv'))
          (mul_mem hm₁ (inv_mem hm₂))
      have h1 := hc.eq_one_of_mem hU1 (hFD hF1).2
      calc X * Y = (X * Y * X⁻¹ * Y⁻¹) * (Y * X) := by group
        _ = Y * X := by rw [h1, one_mul]
    have hle : A ≤ V ⊔ D := by
      intro a ha
      obtain ⟨v, hv, u, hu, d, hd, rfl, hpv⟩ := hc.exists_decomp hxS hVE (hAS ha)
      have hvN := hc.V_le_N hxS hv
      have hv₁N := hc.V_le_N hxS hv₁
      have hv₂N := hc.V_le_N hxS hv₂
      have hσ : P.pf v ∈ Eset := by rw [hpv]; exact hAE _ ((P.mem_im_pf hAN).2 ⟨_, ha, rfl⟩)
      have hfixv : vact (P.pf v) (P.bf u) = P.bf u :=
        (P.comm_iff hvN hu).1 (hsq_vu v hv u hu d hd ha)
      have hc1 := (P.comm_vu hv₁N hvN hu₁ hu (hc.V_comm hv₁ hv)).1
        (hcomm_vu v₁ hv₁ u₁ hu₁ d₁ hd₁ ha₁ v hv u hu d hd ha)
      have hc2 := (P.comm_vu hv₂N hvN hu₂ hu (hc.V_comm hv₂ hv)).1
        (hcomm_vu v₂ hv₂ u₂ hu₂ d₂ hd₂ ha₂ v hv u hu d hd ha)
      rw [hpv₁, hpa₁, swap_inv] at hc1
      rw [hpv₂, hpa₂, swap_inv] at hc2
      have hw : pact (swap 0 1) (P.bf u).1 = (P.bf u).1 ∧
          pact (swap 2 3) (P.bf u).1 = (P.bf u).1 := by
        have hc1' := congrArg Subtype.val hc1
        have hc2' := congrArg Subtype.val hc2
        have hfv := congrArg Subtype.val hfixv
        simp only [vact, AddSubgroup.coe_add] at hc1' hc2' hfv
        rcases (mem_Eset_iff _).1 hσ with h | h | h | h
        · rw [h, inv_one] at hc1' hc2'
          rw [h] at hfv
          have e1 : pact (1 : Perm (Fin 5)) (P.bf u₁).1 = (P.bf u₁).1 := rfl
          have e2 : pact (1 : Perm (Fin 5)) (P.bf u₂).1 = (P.bf u₂).1 := rfl
          rw [e1] at hc1'
          rw [e2] at hc2'
          rw [add_comm (P.bf u₁).1] at hc1'
          rw [add_comm (P.bf u₂).1] at hc2'
          exact ⟨(add_right_cancel hc1').symm, (add_right_cancel hc2').symm⟩
        · rw [h] at hfv
          rw [h, swap_inv] at hc2'
          exact ⟨hfv, (E_comm _ _ hc2'.symm).1⟩
        · rw [h] at hfv
          rw [h, swap_inv] at hc1'
          exact ⟨(E_comm _ _ hc1').2, hfv⟩
        · rw [h] at hfv
          exact fix_prod _ ((mem_evenWeight_iff _).1 (P.bf u).2) hfv
      have hfixE := fixE_of _ hw.1 hw.2
      have huC : u ∈ blockU L ⊓ centralizer (V : Set G) := by
        refine ⟨hu, mem_centralizer_iff.mpr fun v' hv' => ?_⟩
        have hv'N := hc.V_le_N hxS hv'
        have hσ' : P.pf v' ∈ Eset := by
          rw [← mem_Estd, ← hVE]; exact (P.mem_im_pf (hc.V_le_N hxS)).2 ⟨v', hv', rfl⟩
        have := (P.comm_iff hv'N hu).2 (Subtype.ext (hfixE _ hσ'))
        exact this
      rw [(hc.cent_U_V hxS hVE).2.1] at huC
      exact mul_mem (mem_sup_left (mul_mem hv huC.2)) (mem_sup_right hd)
    have hcardVD : Nat.card ↥(V ⊔ D) = Nat.card ↥(S ⊓ centralizer (blockU L : Set G)) := by
      have hN : V ≤ normalizer (D : Set G) := le_normalizer_of_commute hVD
      have h1 := card_sup_mul_card_inf_of_le_normalizer hN
      have hbot : V ⊓ D = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        have hwC : w ∈ V ⊓ centralizer (blockU L : Set G) := ⟨hw.1, (hc.D_le_Q hw.2).2⟩
        rw [← (hc.cent_U_V hxS hVE).2.2] at hwC
        exact hc.eq_one_of_mem hwC.1 hw.2.2
      rw [hbot, Subgroup.card_bot, mul_one, hVdef, card_conjSubgroup, P.card_blockU] at h1
      rw [h1, hcardQ]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardVD]; exact hcard)
  ·
    exfalso
    rw [hcP, hfix] at hbound
    have h2 : Nat.card A < 16 * Nat.card D := by
      calc Nat.card A ≤ (four a₀ b₀).card * (fixOf a₀ b₀).card * Nat.card D := hbound
        _ < 16 * Nat.card D := Nat.mul_lt_mul_of_pos_right h1 Nat.card_pos
    rw [hcardQ] at hcard
    omega

theorem mem_normalizer_conj_Q {x : G} (hxS : x ∈ normalizer (S : Set G))
    (hxR : x ∈ normalizer (R : Set G))
    (hxU : ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G)) {m : G}
    (hmR : m ∈ normalizer (R : Set G))
    (hmF : m ∈ normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G))
    {s₀ : G} (hs₀R : s₀ ∈ R) (hs₀L : s₀ ∈ L) :
    s₀ ∈ normalizer
      ((conjSubgroup (S ⊓ centralizer (blockU L : Set G)) m : Subgroup G) : Set G) := by
  have hs₀N : s₀ ∈ normalizer (L : Set G) := Subgroup.le_normalizer hs₀L
  have hs₀S : s₀ ∈ normalizer (S : Set G) := hc.RS hs₀R
  have hs₀D : s₀ ∈ normalizer ((S ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf hs₀S (mem_normalizer_centralizer hs₀N)
  have hs₀F : s₀ ∈ normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp (conjSubgroup_sqSub_of_mem_normalizer hs₀D)
  have h1 : m * s₀ * m⁻¹ ∈ R := (mem_normalizer_iff.mp hmR s₀).mp hs₀R
  have h2 : m * s₀ * m⁻¹ ∈
      normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) :=
    mul_mem (mul_mem hmF hs₀F) (inv_mem hmF)
  have h3 : m * s₀ * m⁻¹ ∈ normalizer (L : Set G) :=
    hc.mem_normalizer_of_sqSub hxS hxR hxU h1 h2
  have h4 : m * s₀ * m⁻¹ ∈
      normalizer ((S ⊓ centralizer (blockU L : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf (hc.RS h1) (mem_normalizer_centralizer (C1.mem_normalizer_blockU h3))
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_conjSubgroup]
  have e : m * s₀ = (m * s₀ * m⁻¹) * m := by group
  rw [e, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr h4]

theorem conj_Q_cases {x : G} (hxS : x ∈ normalizer (S : Set G))
    (hxR : x ∈ normalizer (R : Set G))
    (hxU : ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G)) {m : G}
    (hmS : m ∈ normalizer (S : Set G)) (hmR : m ∈ normalizer (R : Set G))
    (hmF : m ∈ normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G)) :
    conjSubgroup (S ⊓ centralizer (blockU L : Set G)) m = S ⊓ centralizer (blockU L : Set G) ∨
      conjSubgroup (S ⊓ centralizer (blockU L : Set G)) m =
        conjSubgroup (blockU L) x ⊔ (S ⊓ centralizer (L : Set G)) := by
  obtain ⟨s₀, hs₀R, hs₀L, hD, hE⟩ := hc.exists_swapper
  exact hc.eq_of_modElem hxS (hc.im_V_eq hxS hxR hxU) (hc.modElem_Q.conj hmS hmF)
    (by rw [card_conjSubgroup]) (Subgroup.le_normalizer hs₀L)
    (hc.mem_normalizer_conj_Q hxS hxR hxU hmR hmF hs₀R hs₀L) hD hE

theorem hor {x : G} (hxS : x ∈ normalizer (S : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hxU : ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G)) {m : G}
    (hmS : m ∈ normalizer (S : Set G)) (hmR : m ∈ normalizer (R : Set G))
    (hmF : m ∈ normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G)) :
    m ∈ normalizer ((S ⊓ centralizer (blockU L : Set G) : Subgroup G) : Set G) ∨
      m * x⁻¹ ∈ normalizer ((S ⊓ centralizer (blockU L : Set G) : Subgroup G) : Set G) := by
  have hxF := hc.mem_normalizer_sqSub hxS hxR hxU
  have hQx : conjSubgroup (S ⊓ centralizer (blockU L : Set G)) x =
      conjSubgroup (blockU L) x ⊔ (S ⊓ centralizer (L : Set G)) := by
    refine (hc.conj_Q_cases hxS hxR hxU hxS hxR hxF).resolve_left fun h => hxU ?_
    have := conjSubgroup_mono hc.U_le_Q x
    rw [h] at this
    exact this.trans inf_le_right
  rcases hc.conj_Q_cases hxS hxR hxU hmS hmR hmF with h | h
  · exact Or.inl (conjSubgroup_eq_iff_mem_normalizer.mp h)
  · right
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, h, ← hQx,
      conjSubgroup_conjSubgroup_inv]

theorem conj_le_of_odd {y : G} (hyS : y ∈ normalizer (S : Set G))
    (hyR : y ∈ normalizer (R : Set G)) (hodd : Odd (orderOf y)) :
    conjSubgroup (blockU L) y ≤ centralizer (blockU L : Set G) := by
  by_contra hyU
  have hyF := hc.mem_normalizer_sqSub hyS hyR hyU
  set M₁ : Subgroup G := normalizer (S : Set G) ⊓ normalizer (R : Set G) ⊓
    normalizer ((sqSub (S ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) with hM₁
  have hyM : y ∈ M₁ := ⟨⟨hyS, hyR⟩, hyF⟩
  have h := conj_le_of_odd_of_hor (M₁ := M₁) hyM hc.U_le_Q
    (fun m hm => hc.hor hyS hyR hyU hm.1.1 hm.1.2 hm.2) hodd
  exact hyU (h.trans inf_le_right)

theorem exists_good_elt {T M₀ : Subgroup G} (hT : IsSylowTwoOf T M₀)
    (hM₀S : M₀ ≤ normalizer (S : Set G)) (hM₀R : M₀ ≤ normalizer (R : Set G))
    (hidx : (T ⊓ normalizer (L : Set G)).relIndex T ≤ 2) {y : G} (hyM₀ : y ∈ M₀)
    (hyU : ¬ conjSubgroup (blockU L) y ≤ centralizer (blockU L : Set G)) :
    ¬ T ≤ normalizer (L : Set G) ∧ ∃ x ∈ M₀,
      x ∈ normalizer ((T ⊓ normalizer (L : Set G) : Subgroup G) : Set G) ∧
      ¬ conjSubgroup (blockU L) x ≤ centralizer (blockU L : Set G) := by
  have hyS := hM₀S hyM₀
  have hyR := hM₀R hyM₀
  have hVE := hc.im_V_eq hyS hyR hyU
  exact exists_good_elt_of_hor hT hM₀S hidx rfl hc.D_eq hc.QD hc.US hyM₀
    (hc.mem_normalizer_sqSub hyS hyR hyU) (fun h => hyU (h.trans inf_le_right))
    (fun m hm => hc.hor hyS hyR hyU (hM₀S hm.1) (hM₀R hm.1) hm.2)
    (fun g hg => hc.conj_D_le hyS hVE (hM₀S hg.1) hg.2)

end A5Cfg

end CFSG.Quasithin.C58NS
