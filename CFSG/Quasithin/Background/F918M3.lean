module

public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.F918M1
import CFSG.Quasithin.EmptyFaithful.S153EB6L
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

section Helpers

variable {V : Type} [CommGroup V]

private def d29TrivSec (S : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | (∀ s ∈ S, g s = s) ∧ ∀ v, g v * v⁻¹ ∈ S}
  one_mem' := ⟨fun _ _ => rfl, fun v => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun s hs => ?_, fun v => ?_⟩
    · show g (h s) = s
      rw [hh1 s hs, hg1 s hs]
    · have e : (g * h) v * v⁻¹ = (g (h v) * (h v)⁻¹) * (h v * v⁻¹) := by
        show g (h v) * v⁻¹ = _
        group
      rw [e]
      exact S.mul_mem (hg2 _) (hh2 v)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun s hs => ?_, fun v => ?_⟩
    · apply g.injective
      rw [MulAut.apply_inv_self, hg1 s hs]
    · have := S.inv_mem (hg2 (g⁻¹ v))
      rwa [MulAut.apply_inv_self, mul_inv_rev, inv_inv] at this

private theorem d29TrivSec_mul_self (hV : ∀ v : V, v ^ 2 = 1) {S : Subgroup V} {g : MulAut V}
    (hg : g ∈ d29TrivSec S) : g * g = 1 := by
  refine MulEquiv.ext fun v => ?_
  obtain ⟨d, hdS, hdv⟩ : ∃ d ∈ S, g v = d * v :=
    ⟨g v * v⁻¹, hg.2 v, by rw [inv_mul_cancel_right]⟩
  show g (g v) = v
  rw [hdv, map_mul, hg.1 d hdS, hdv, ← mul_assoc, ← sq, hV d, one_mul]

end Helpers

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem d29_further_small (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)} {I I' : Subgroup V}
    (hS : TwoSummands G I I') (hAG : A ≤ G) (hAe : IsElemAbelian2 A) {a : MulAut V} (haA : a ∈ A)
    (haI : a ∉ stabSub I) {c : V} (hcI : c ∈ I) (hc1 : c ≠ 1)
    (hBc : ∀ b ∈ A ⊓ stabSub I, ∀ x ∈ I, b x = x ∨ b x = x * c)
    (hfull : ∀ t : MulAut ↥I, IsTransvectionWith t (⟨c, hcI⟩ : ↥I) →
      t ∈ autSub (A ⊓ stabSub I) I)
    (J : Subgroup V) (hJI : J ≤ I) (hcJ : c ∈ J) (hJne : J ≠ I)
    (hJN : ∀ n ∈ G ⊓ stabSub I, ∀ x ∈ J, n x ∈ J) :
    pCoreOf 2 G ≠ ⊥ := by
  have haG : a ∈ G := hAG haA
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hAe.2 a haA
  obtain ⟨hI1, -⟩ := hS.map_eq_of_swap haG haI
  have haa : ∀ x : V, a (a x) = x := fun x => by
    have := congrArg (fun g : MulAut V => g x) ha2
    simpa using this
  set J' : Subgroup V := J.map a.toMonoidHom
  have haJ : ∀ x ∈ J, a x ∈ J' := fun x hx => ⟨x, hx, rfl⟩
  set S : Subgroup V := J ⊔ J'
  have hNJ' : ∀ n ∈ G ⊓ stabSub I, ∀ y ∈ J', n y ∈ J' := by
    rintro n hn _ ⟨x, hx, rfl⟩
    have hconj : a⁻¹ * n * a ∈ G ⊓ stabSub I := by
      refine ⟨G.mul_mem (G.mul_mem (G.inv_mem haG) hn.1) haG, ?_⟩
      have := hS.conj_mem_stab (G.inv_mem haG) hn.1 hn.2
      simpa using this
    refine ⟨(a⁻¹ * n * a) x, hJN _ hconj x hx, ?_⟩
    simp
  have haS : ∀ s ∈ S, a s ∈ S := by
    intro s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp hs
    obtain ⟨z, hz, rfl⟩ := hy
    rw [map_mul]
    refine S.mul_mem (Subgroup.mem_sup_right (haJ x hx)) ?_
    have : a (a.toMonoidHom z) = z := haa z
    rw [this]
    exact Subgroup.mem_sup_left hz
  have hNS : ∀ n ∈ G ⊓ stabSub I, ∀ s ∈ S, n s ∈ S := by
    intro n hn s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp hs
    rw [map_mul]
    exact S.mul_mem (Subgroup.mem_sup_left (hJN n hn x hx))
      (Subgroup.mem_sup_right (hNJ' n hn y hy))
  have hGS : ∀ g ∈ G, ∀ s ∈ S, g s ∈ S := by
    intro g hg s hs
    by_cases hgI : g ∈ stabSub I
    · exact hNS g ⟨hg, hgI⟩ s hs
    · have hn2 : a⁻¹ * g ∈ stabSub I := by
        have h1 := (hS.map_eq_of_swap hg hgI).1
        have h2 := (hS.map_eq_of_swap (G.inv_mem haG)
          (fun h => haI (by simpa using (stabSub I).inv_mem h))).2
        rw [mem_stabSub_iff_map_eq, map_mul_aut', h1, h2]
      have hn : a⁻¹ * g ∈ G ⊓ stabSub I := ⟨G.mul_mem (G.inv_mem haG) hg, hn2⟩
      have : g s = a ((a⁻¹ * g) s) := by simp
      rw [this]
      exact haS _ (hNS _ hn s hs)
  have hnormY :
      G ≤ Subgroup.normalizer ((G ⊓ d29TrivSec S : Subgroup (MulAut V)) : Set (MulAut V)) := by
    have key : ∀ g ∈ G, ∀ y ∈ G ⊓ d29TrivSec S, g * y * g⁻¹ ∈ G ⊓ d29TrivSec S := by
      intro g hg y hy
      refine ⟨G.mul_mem (G.mul_mem hg hy.1) (G.inv_mem hg), fun s hs => ?_, fun v => ?_⟩
      · show g (y (g⁻¹ s)) = s
        rw [hy.2.1 _ (hGS g⁻¹ (G.inv_mem hg) s hs), MulAut.apply_inv_self]
      · have e : (g * y * g⁻¹) v * v⁻¹ = g (y (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
          simp [map_mul, map_inv]
        rw [e]
        exact hGS g hg _ (hy.2.2 _)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key g hg y hy, fun hy => ?_⟩
    have := key g⁻¹ (G.inv_mem hg) _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at this
  have hY2 : IsPGroup 2 ↥(G ⊓ d29TrivSec S) := fun y => ⟨1, by
    refine Subtype.ext ?_
    simp only [pow_one, Subgroup.coe_one, pow_two]
    exact d29TrivSec_mul_self hV y.2.2⟩
  have hYle : G ⊓ d29TrivSec S ≤ pCoreOf 2 G :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnormY hY2
  have hc1' : (⟨c, hcI⟩ : ↥I) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hJtop : J.subgroupOf I ≠ ⊤ := by
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hJne (le_antisymm hJI h)
  obtain ⟨t, htv, ht1, htJ⟩ := exists_transvection_trivial_on hV I ⟨c, hcI⟩ hc1'
    (J.subgroupOf I) (Subgroup.mem_subgroupOf.mpr hcJ) hJtop
  obtain ⟨g, hgA, hgt⟩ := mem_autSub.mp (hfull t htv)
  have hβA : (g : MulAut V) ∈ A := hgA.1
  have hβJ : ∀ x ∈ J, (g : MulAut V) x = x := by
    intro x hx
    have := htJ ⟨x, hJI hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
    rw [← hgt] at this
    exact congrArg Subtype.val this
  have hβa : ∀ x : V, (g : MulAut V) (a x) = a ((g : MulAut V) x) := fun x => by
    have := congrArg (fun h : MulAut V => h x) (hAe.1 (g : MulAut V) hβA a haA)
    simpa using this
  have hβJ' : ∀ y ∈ J', (g : MulAut V) y = y := by
    rintro _ ⟨x, hx, rfl⟩
    show (g : MulAut V) (a x) = a x
    rw [hβa, hβJ x hx]
  have hβS : ∀ s ∈ S, (g : MulAut V) s = s := by
    intro s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp hs
    rw [map_mul, hβJ x hx, hβJ' y hy]
  have hβδ : ∀ v, (g : MulAut V) v * v⁻¹ ∈ S := by
    intro v
    have hv : v ∈ I ⊔ I' := by rw [hS.sup]; exact Subgroup.mem_top v
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp hv
    have hβB : (g : MulAut V) ∈ A ⊓ stabSub I := ⟨hβA, g.2⟩
    have h1 : (g : MulAut V) x * x⁻¹ ∈ S := by
      rcases hBc _ hβB x hx with h | h
      · rw [h, mul_inv_cancel]
        exact S.one_mem
      · rw [h, mul_comm x c, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left hcJ
    have h2 : (g : MulAut V) y * y⁻¹ ∈ S := by
      rw [← hI1] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      show (g : MulAut V) (a z) * (a z)⁻¹ ∈ S
      rcases hBc _ hβB z hz with h | h
      · rw [hβa, h, mul_inv_cancel]
        exact S.one_mem
      · have : (g : MulAut V) (a z) = a z * a c := by rw [hβa, h, map_mul]
        rw [this, mul_comm (a z) (a c), mul_inv_cancel_right]
        exact Subgroup.mem_sup_right (haJ c hcJ)
    have e : (g : MulAut V) (x * y) * (x * y)⁻¹ =
        ((g : MulAut V) x * x⁻¹) * ((g : MulAut V) y * y⁻¹) := by
      rw [map_mul, mul_inv]
      exact mul_mul_mul_comm _ _ _ _
    rw [e]
    exact S.mul_mem h1 h2
  have hβ1 : (g : MulAut V) ≠ 1 := by
    intro h
    apply ht1
    have hg1 : g = 1 := Subtype.ext h
    rw [← hgt, hg1, map_one]
  have hβY : (g : MulAut V) ∈ G ⊓ d29TrivSec S := ⟨hAG hβA, hβS, hβδ⟩
  intro hbot
  have := hYle hβY
  rw [hbot, Subgroup.mem_bot] at this
  exact hβ1 this

theorem d29_further_kernel (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)} {I I' : Subgroup V}
    (hS : TwoSummands G I I') (hi : 2 < rk I) {a : MulAut V} (haG : a ∈ G) (haI : a ∉ stabSub I)
    (htop : autSub (G ⊓ stabSub I) I = ⊤) (hker : G ⊓ centSub I ≠ ⊥) :
    ∃ A₀ : Subgroup (MulAut V), IsA2 G A₀ ∧ commSeries A₀ 2 = ⊥ ∧ rAV A₀ ≤ 1 := by
  obtain ⟨hI1, hI2⟩ := hS.map_eq_of_swap haG haI
  have hI'a : ∀ y ∈ I', a y ∈ I := fun y hy => by rw [← hI2]; exact ⟨y, hy, rfl⟩
  have hIainv : ∀ x ∈ I, a⁻¹ x ∈ I' := by
    intro x hx
    rw [← hI2] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hI'ainv : ∀ y ∈ I', a⁻¹ y ∈ I := by
    intro y hy
    rw [← hI1] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  have hV' : ∀ v : ↥I, v ^ 2 = 1 := fun v => Subtype.ext (hV v)
  have hsimple : IsSimpleGroup (MulAut ↥I) :=
    S153EB6.isSimple_mulAut hV' (n := rk I) (by omega) (card_eq_two_pow hV I)
  have hnorm : (autSub (G ⊓ centSub I') I).Normal := by
    refine ⟨fun ρ hρ θ => ?_⟩
    have hθ : θ ∈ autSub (G ⊓ stabSub I) I := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨m, hmN, rfl⟩ := mem_autSub.mp hθ
    obtain ⟨k, hkK, rfl⟩ := mem_autSub.mp hρ
    rw [mem_autSub]
    have hm' : (m : MulAut V) ∈ stabSub I' := (hS.mem_stab_iff hmN.1).mpr hmN.2
    refine ⟨m * k * m⁻¹, ⟨?_, ?_⟩, ?_⟩
    · exact G.mul_mem (G.mul_mem hmN.1 hkK.1) (G.inv_mem hmN.1)
    · intro y hy
      have h1 : (m : MulAut V)⁻¹ y ∈ I' := ((stabSub I').inv_mem hm' y).mpr hy
      show (m : MulAut V) ((k : MulAut V) ((m : MulAut V)⁻¹ y)) = y
      rw [hkK.2 _ h1, MulAut.apply_inv_self]
    · simp [map_mul, map_inv]
  have hne : autSub (G ⊓ centSub I') I ≠ ⊥ := by
    obtain ⟨k0, hk0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
    have hk1G : a⁻¹ * (k0 : MulAut V) * a ∈ G :=
      G.mul_mem (G.mul_mem (G.inv_mem haG) k0.2.1) haG
    have hk1C : a⁻¹ * (k0 : MulAut V) * a ∈ centSub I' := by
      intro y hy
      show a⁻¹ ((k0 : MulAut V) (a y)) = y
      rw [k0.2.2 _ (hI'a y hy)]
      simp
    have hk1ne : a⁻¹ * (k0 : MulAut V) * a ≠ 1 := by
      intro h
      apply hk0
      have : (k0 : MulAut V) = 1 := by
        have e : (k0 : MulAut V) = a * (a⁻¹ * (k0 : MulAut V) * a) * a⁻¹ := by group
        rw [e, h]
        group
      exact Subtype.ext this
    have hk1I : a⁻¹ * (k0 : MulAut V) * a ∈ stabSub I :=
      (hS.mem_stab_iff hk1G).mp (centSub_le_stabSub I' hk1C)
    intro hbot
    have hmem : resHom I ⟨a⁻¹ * (k0 : MulAut V) * a, hk1I⟩ ∈ autSub (G ⊓ centSub I') I :=
      mem_autSub.mpr ⟨⟨_, hk1I⟩, ⟨hk1G, hk1C⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hk1ne
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ I ⊔ I' := by rw [hS.sup]; exact Subgroup.mem_top v
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp hv
    have hx'' := DFunLike.congr_fun hmem (⟨x, hx⟩ : ↥I)
    have hx' : (a⁻¹ * (k0 : MulAut V) * a) x = x := congrArg Subtype.val hx''
    show (a⁻¹ * (k0 : MulAut V) * a) (x * y) = x * y
    rw [map_mul, hx', hk1C y hy]
  have hK2top : autSub (G ⊓ centSub I') I = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hne
  have hIbot : I ≠ ⊥ := by
    rintro rfl
    rw [rk_bot] at hi
    omega
  obtain ⟨c0, hc0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hIbot
  have hJtop : Subgroup.zpowers c0 ≠ ⊤ := by
    intro h
    have h1 : Nat.card (Subgroup.zpowers c0) = Nat.card ↥I := by rw [h, Subgroup.card_top]
    have h2 : orderOf c0 ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hV' c0))
    rw [Nat.card_zpowers, card_eq_two_pow hV I] at h1
    have h3 : 2 ^ 3 ≤ 2 ^ rk I := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨τ, hτ, hτ1, -⟩ := exists_transvection_trivial_on hV I c0 hc0 (Subgroup.zpowers c0)
    (Subgroup.mem_zpowers c0) hJtop
  obtain ⟨k2, hk2, hk2τ⟩ := mem_autSub.mp (hK2top ▸ Subgroup.mem_top τ :
    τ ∈ autSub (G ⊓ centSub I') I)
  set k : MulAut V := a * (k2 : MulAut V) * a⁻¹ with hk
  have hkG : k ∈ G := G.mul_mem (G.mul_mem haG hk2.1) (G.inv_mem haG)
  have hkI : ∀ x ∈ I, k x = x := by
    intro x hx
    show a ((k2 : MulAut V) (a⁻¹ x)) = x
    rw [hk2.2 _ (hIainv x hx), MulAut.apply_inv_self]
  have hkI' : ∀ y ∈ I', k y = y ∨ k y = y * a (c0 : V) := by
    intro y hy
    have h1 := hτ.2 ⟨a⁻¹ y, hI'ainv y hy⟩
    have h2 : ∀ z : ↥I, ((τ z : ↥I) : V) = (k2 : MulAut V) (z : V) := fun z => by
      rw [← hk2τ]
      rfl
    show a ((k2 : MulAut V) (a⁻¹ y)) = y ∨ a ((k2 : MulAut V) (a⁻¹ y)) = y * a (c0 : V)
    rcases h1 with h | h
    · left
      have := congrArg Subtype.val h
      rw [h2] at this
      rw [this]
      simp
    · right
      have := congrArg Subtype.val h
      rw [h2] at this
      rw [Subgroup.coe_mul] at this
      rw [this, map_mul]
      simp
  have hw1 : a (c0 : V) ≠ 1 := by
    intro h
    apply hc0
    apply Subtype.ext
    have : (c0 : V) = 1 := by
      have := congrArg (fun z => a⁻¹ z) h
      simpa using this
    exact this
  have htw : IsTransvectionWith k (a (c0 : V)) := by
    refine ⟨hw1, fun v => ?_⟩
    have hv : v ∈ I ⊔ I' := by rw [hS.sup]; exact Subgroup.mem_top v
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul, hkI x hx]
    rcases hkI' y hy with h | h
    · left
      rw [h]
    · right
      rw [h, mul_assoc]
  have hk1 : k ≠ 1 := by
    intro h
    apply hτ1
    rw [← hk2τ]
    have : (k2 : MulAut V) = 1 := by
      have e : (k2 : MulAut V) = a⁻¹ * k * a := by rw [hk]; group
      rw [e, h]
      group
    have hk21 : k2 = 1 := Subtype.ext this
    rw [hk21, map_one]
  have hsq : k ^ 2 = 1 := by rw [pow_two]; exact B1.tv_sq hV htw hk1
  have hA2 : IsA2 G (Subgroup.zpowers k) :=
    ⟨Subgroup.zpowers_le.mpr hkG, fun h => hk1 (Subgroup.zpowers_eq_bot.mp h),
      B1.isElemAbelian2_zpowers_tv hV hk1 htw⟩
  refine ⟨Subgroup.zpowers k, hA2,
    (isQuadratic_iff_commSeries_two _).mp (isQuadratic_zpowers hV hsq), ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (rAV_le_one_iff hV hA2).mpr ?_
  rw [Nat.card_zpowers, orderOf_eq_prime hsq hk1]
  exact (B1.card_eq_two_mul_fixV_of_tv hV hk1 htw).le

end CFSG.Quasithin
