module

public import CFSG.Quasithin.H13.A6S13821zk

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.F7 CFSG.Quasithin.InternalSec

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

theorem exists_two_part_mem {H Q K T : Subgroup G} (hQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hT : IsSylowTwoOf T H) {c s : G} (hcH : c ∈ H)
    (hconj : ∀ h ∈ H, h * c * h⁻¹ * c⁻¹ ∈ Q ∨ h * c * h⁻¹ * c ∈ Q) (hsH : s ∈ H)
    (hs2 : ∃ e : ℕ, s ^ 2 ^ e = 1) (hsc : s * c * s⁻¹ * c ∈ Q)
    (hsK : ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ Q) :
    ∃ s' ∈ T, (∃ e : ℕ, s' ^ 2 ^ e = 1) ∧ s' * c * s'⁻¹ * c ∈ Q ∧
      ∀ k ∈ K, s' * k * s'⁻¹ * k⁻¹ ∈ Q := by
  have hconjQ : ∀ g ∈ H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQ hg) q).mp hq
  obtain ⟨e, he⟩ := hs2
  obtain ⟨g, hgH, hgs⟩ : ∃ g ∈ H, g⁻¹ * s * g ∈ T := by
    have hord : orderOf s ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one he
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hcard : Nat.card (Subgroup.zpowers s) = 2 ^ j := by rw [Nat.card_zpowers, hj]
    have h2 : IsPGroup 2 (Subgroup.zpowers s) := IsPGroup.of_card hcard
    obtain ⟨S, hS, hsS⟩ := A4.exists_isSylowTwoOf_ge (Subgroup.zpowers_le.mpr hsH) h2
    obtain ⟨h, hh, hSh⟩ := A4.exists_conj_of_isSylowTwoOf hT hS
    exact ⟨h, hh, (hSh s).mp (hsS (Subgroup.mem_zpowers s))⟩
  refine ⟨g⁻¹ * s * g, hgs, ⟨e, ?_⟩, ?_, ?_⟩
  · have : (g⁻¹ * s * g) ^ 2 ^ e = g⁻¹ * s ^ 2 ^ e * g := by
      have h := conj_pow (a := g⁻¹) (b := s) (i := 2 ^ e)
      simpa using h
    rw [this, he, mul_one, inv_mul_cancel]
  ·
    set c' := g * c * g⁻¹ with hc'
    have key : s * c' * s⁻¹ * c' ∈ Q := by
      rcases hconj g hgH with h1 | h1
      · have e1 : s * c' * s⁻¹ * c' = s * (c' * c⁻¹) * s⁻¹ * (s * c * s⁻¹ * c) *
            (c⁻¹ * (c' * c⁻¹) * c⁻¹⁻¹) := by group
        rw [e1]
        exact Q.mul_mem (Q.mul_mem (hconjQ s hsH _ h1) hsc)
          (hconjQ c⁻¹ (H.inv_mem hcH) _ h1)
      · have e1 : s * c' * s⁻¹ * c' = s * (c' * c) * s⁻¹ *
            (c * (s * c * s⁻¹ * c)⁻¹ * c⁻¹) * (c * (c' * c) * c⁻¹) := by group
        rw [e1]
        exact Q.mul_mem (Q.mul_mem (hconjQ s hsH _ h1) (hconjQ c hcH _ (Q.inv_mem hsc)))
          (hconjQ c hcH _ h1)
    have e1 : g⁻¹ * s * g * c * (g⁻¹ * s * g)⁻¹ * c = g⁻¹ * (s * c' * s⁻¹ * c') * g⁻¹⁻¹ := by
      rw [hc']; group
    rw [e1]
    exact hconjQ g⁻¹ (H.inv_mem hgH) _ key
  · intro k hk
    have hk' : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKn hgH) k).mp hk
    have e1 : g⁻¹ * s * g * k * (g⁻¹ * s * g)⁻¹ * k⁻¹ =
        g⁻¹ * (s * (g * k * g⁻¹) * s⁻¹ * (g * k * g⁻¹)⁻¹) * g⁻¹⁻¹ := by group
    rw [e1]
    exact hconjQ g⁻¹ (H.inv_mem hgH) _ (hsK _ hk')

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  F1.le_normalizer_sup (X := Subgroup.zpowers g) (Subgroup.zpowers_le.mpr hA)
    (Subgroup.zpowers_le.mpr hB) (Subgroup.mem_zpowers g)

omit [Finite G] in
theorem mem_normalizer_conjSub {I : Subgroup G} {c g : G}
    (h : c⁻¹ * g * c ∈ Subgroup.normalizer (I : Set G)) :
    g ∈ Subgroup.normalizer ((conjSub c I : Subgroup G) : Set G) := by
  rw [conjSub_normalizer, mem_conjSub]
  exact h

theorem conj_mem_normalizer_sup {V₁ U I : Subgroup G} {c : G} (hV₁I : V₁ ≤ I) (hIU : I ≤ U)
    (hθ : ∀ u ∈ U, u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ∈ V₁) :
    c ∈ Subgroup.normalizer ((I ⊔ conjSub c I : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hle : I ⊔ conjSub c I ≤ (I ⊔ conjSub c I).comap (MulAut.conj c).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_right (mul_mem_conjSub ha)
    · rw [mem_conjSub] at hb
      set i := c⁻¹ * b * c with hi
      have hb' : b = c * i * c⁻¹ := by rw [hi]; group
      have hv := hθ i (hIU hb)
      show c * b * c⁻¹ ∈ I ⊔ conjSub c I
      have e : c * b * c⁻¹ = (c * i * c⁻¹)⁻¹ * i⁻¹ *
          (i * (c * i * c⁻¹) * (c * (c * i * c⁻¹) * c⁻¹)) := by
        rw [hb']; group
      rw [e]
      refine (I ⊔ conjSub c I).mul_mem ((I ⊔ conjSub c I).mul_mem ?_ ?_) ?_
      · exact (I ⊔ conjSub c I).inv_mem (Subgroup.mem_sup_right (mul_mem_conjSub hb))
      · exact (I ⊔ conjSub c I).inv_mem (Subgroup.mem_sup_left hb)
      · exact Subgroup.mem_sup_left (hV₁I hv)
  exact hle hn

theorem sup_conj_le_normalizer {V₁ U I Q K T X : Subgroup G} {c : G} (hV₁I : V₁ ≤ I)
    (hIU : I ≤ U) (hθ : ∀ u ∈ U, u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ∈ V₁)
    (hQT : Q ≤ T) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    (hKI : K ≤ Subgroup.normalizer (I : Set G)) (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hTX : ∀ t ∈ T, t * c * t⁻¹ ∈ X)
    (htri : ∀ y ∈ X, y ∈ Q ∨ y * c⁻¹ ∈ Q ∨ y * c ∈ Q) :
    K ⊔ T ≤ Subgroup.normalizer ((I ⊔ conjSub c I : Subgroup G) : Set G) ∧
      c ∈ Subgroup.normalizer ((I ⊔ conjSub c I : Subgroup G) : Set G) := by
  set J := I ⊔ conjSub c I with hJ
  have hcJ : c ∈ Subgroup.normalizer (J : Set G) := conj_mem_normalizer_sup hV₁I hIU hθ
  have hQJ : Q ≤ Subgroup.normalizer (J : Set G) := by
    intro q hq
    refine mem_normalizer_sup (hTI (hQT hq)) (mem_normalizer_conjSub (hTI (hQT ?_)))
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcQ) q).mp hq
    simpa using h
  refine ⟨sup_le (fun k hk => ?_) (fun t ht => ?_), hcJ⟩
  · refine mem_normalizer_sup (hKI hk) (mem_normalizer_conjSub (hKI ?_))
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcK) k).mp hk
    simpa using h
  ·
    have hy : t * c * t⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
      rcases htri _ (hTX t ht) with h | h | h
      · exact hQJ h
      · have e : t * c * t⁻¹ = (t * c * t⁻¹ * c⁻¹) * c := by group
        rw [e]
        exact Subgroup.mul_mem _ (hQJ h) hcJ
      · have e : t * c * t⁻¹ = (t * c * t⁻¹ * c) * c⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ (hQJ h) (Subgroup.inv_mem _ hcJ)
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hle : J ≤ J.comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTI ht) a).mp ha)
      · rw [mem_conjSub] at hb
        show t * b * t⁻¹ ∈ J
        have e : t * b * t⁻¹ = (t * c * t⁻¹) * (t * (c⁻¹ * b * c) * t⁻¹) *
            (t * c * t⁻¹)⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp hy _).mp
          (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTI ht) _).mp hb))
    exact hle hn

omit [Finite G] in
theorem mem_stabSub_sup {W : Type*} [CommGroup W] {A B : Subgroup W} {g : MulAut W}
    (hA : g ∈ stabSub A) (hB : g ∈ stabSub B) : g ∈ stabSub (A ⊔ B) := by
  have key : ∀ h : MulAut W, h ∈ stabSub A → h ∈ stabSub B → ∀ v ∈ A ⊔ B, h v ∈ A ⊔ B := by
    intro h hA' hB' v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup ((hA' a).mpr ha) ((hB' b).mpr hb)
  intro v
  refine ⟨fun hv => ?_, key g hA hB v⟩
  have h1 := key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hv
  simpa using h1

theorem inf_conj_le_centralizerMod {T V L V₁ Vp H K I : Subgroup G}
    (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirrT : IsIrrPlusTildeT hF hIU)
    (hTI : T ≤ Subgroup.normalizer (I : Set G)) {x : G} (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hθ : ∀ u ∈ conjClosure Vp H, u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ V₁)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {t : G} (htT : t ∈ T)
    (htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) (htx : t * x * t⁻¹ * x ∈ pCoreOf 2 H)
    {e : ℕ} (ht2 : t ^ 2 ^ e = 1) :
    I ⊓ conjSub x I ≤ centralizerMod V₁ I K := by
  classical
  have := factElem hF hIU
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have htH : t ∈ H := hTH htT
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirrT
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  set ψ := actH hF.H_le_normalizer_V₁ hIH with hψ
  obtain ⟨hy3, hcube, hr2, hry, hyL, hrL⟩ := cube_facts hF hIU hxH hx3 hθ hxK htH htK htx ht2
  set U := subM V₁ (conjClosure I H) I with hU
  set Lk := autIH V₁ I H K with hLk
  set y := ψ ⟨x, hxH⟩ with hy
  set r := ψ ⟨t, htH⟩ with hr
  have hW2 : ∀ w : ↥(tildeOf V₁ (conjClosure I H)), w ^ 2 = 1 := by
    intro w
    apply Subtype.ext
    simpa using (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).2 w w.2
  have hfixC : XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) U = U ⊓ fixV Lk := by
    ext u
    constructor
    · rintro ⟨hu, hf⟩
      exact ⟨hu, fun γ hγ => hf ⟨γ, hMp ▸ hγ⟩⟩
    · rintro ⟨hu, hc⟩
      exact ⟨hu, fun a => hc a (hMp ▸ a.2)⟩
  have hUinv : ∀ γ ∈ Lk, ∀ w ∈ U, γ w ∈ U := fun γ hγ w hw =>
    hirr'.1.2.1 ⟨γ, hMp ▸ hγ⟩ w hw
  have hUst : ∀ γ ∈ Lk, γ ∈ stabSub U := by
    intro γ hγ u
    refine ⟨fun h => ?_, hUinv γ hγ u⟩
    have h1 := hUinv γ⁻¹ (Lk.inv_mem hγ) _ h
    simpa using h1
  have hDst : ∀ γ ∈ Lk, γ ∈ stabSub (fixV Lk) := fun γ hγ =>
    L32A.C.mem_stabSub_fixV_of_conj (fun m hm => Lk.mul_mem (Lk.mul_mem hγ hm) (Lk.inv_mem hγ))
      (fun m hm => Lk.mul_mem (Lk.mul_mem (Lk.inv_mem hγ) hm) hγ)
  have hyD : y ∈ stabSub (fixV Lk) := mem_stabSub_fixV_of_commute hyL
  have hrD : r ∈ stabSub (fixV Lk) := mem_stabSub_fixV_of_commute hrL
  have hrU : r ∈ stabSub U := (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ hIHN hIH hV₁I
    (le_conjClosure I H) ⟨t, htH⟩).mpr (hTI htT)
  set Ux := U.map y.toMonoidHom with hUx
  have hUxinv : ∀ γ ∈ Lk, ∀ w ∈ Ux, γ w ∈ Ux := by
    rintro γ hγ _ ⟨u, hu, rfl⟩
    refine ⟨γ u, hUinv γ hγ u hu, ?_⟩
    have h1 := congrArg (fun f : MulAut _ => f u) (hyL γ hγ)
    exact h1.symm
  have hnt : ∃ γ ∈ Lk, ∃ v ∈ U, γ v * v⁻¹ ∉ fixV Lk := by
    by_contra hcon
    push Not at hcon
    have hle : XMod.commOf ↥(autIH V₁ I H (conjClosure K T)) U ≤ U ⊓ fixV Lk := by
      rw [XMod.commOf, Subgroup.closure_le]
      rintro _ ⟨a, l, hl, rfl⟩
      have ha : (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈ Lk := hMp ▸ a.2
      exact ⟨U.mul_mem (hirr'.1.2.1 a l hl) (U.inv_mem hl), hcon _ ha l hl⟩
    rw [hirr'.1.2.2.1] at hle
    apply hirr'.1.2.2.2.1.ne
    rw [hfixC]
    exact le_antisymm inf_le_left (le_inf le_rfl (hle.trans inf_le_right))
  have hP : (U ⊓ Ux) ⊔ (U ⊓ fixV Lk) = U ⊓ fixV Lk ∨ (U ⊓ Ux) ⊔ (U ⊓ fixV Lk) = U := by
    have h := hirr'.1.2.2.2.2 ((U ⊓ Ux) ⊔ (U ⊓ fixV Lk)) ?_ ?_ ?_
    · rwa [hfixC] at h
    · intro a l hl
      have ha : (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈ Lk := hMp ▸ a.2
      show (a : MulAut _) l ∈ (U ⊓ Ux) ⊔ (U ⊓ fixV Lk)
      obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.mp hl
      rw [map_mul]
      exact Subgroup.mul_mem_sup ⟨hUinv _ ha p hp.1, hUxinv _ ha p hp.2⟩
        ⟨hUinv _ ha q hq.1, (hDst _ ha q).mpr hq.2⟩
    · rw [hfixC]; exact le_sup_right
    · exact sup_le inf_le_left inf_le_left
  have hmain : U ⊓ Ux ≤ fixV Lk := by
    rcases hP with hP | hP
    · intro w hw
      have h1 : w ∈ (U ⊓ Ux) ⊔ (U ⊓ fixV Lk) := Subgroup.mem_sup_left hw
      rw [hP] at h1
      exact h1.2
    ·
      exfalso
      set A := U ⊔ fixV Lk with hA
      have hUle : U ≤ Ux ⊔ fixV Lk := by
        rw [← hP]
        exact sup_le_sup inf_le_right inf_le_right
      have hDmap : (fixV Lk).map y.toMonoidHom = fixV Lk := by
        ext v
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact (hyD w).mpr hw
        · intro hv
          refine ⟨y⁻¹ v, ?_, by simp⟩
          exact ((Subgroup.inv_mem _ hyD) v).mpr hv
      have hAmap : A.map y.toMonoidHom = A := by
        have hle : A ≤ A.map y.toMonoidHom := by
          rw [hA, Subgroup.map_sup, hDmap]
          exact sup_le hUle le_sup_right
        refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
        exact (Subgroup.card_map_of_injective (f := y.toMonoidHom) y.injective).le
      have hyA : y ∈ stabSub A := by
        intro v
        constructor
        · intro hv
          rw [← hAmap] at hv
          obtain ⟨w, hw, hwv⟩ := hv
          have : w = v := y.injective hwv
          rw [← this]
          exact hw
        · intro hv
          rw [← hAmap]
          exact ⟨v, hv, rfl⟩
      have hrA : r ∈ stabSub A := mem_stabSub_sup hrU hrD
      have hLA : Lk ≤ stabSub A ⊓ stabSub (fixV Lk) := fun γ hγ =>
        ⟨mem_stabSub_sup (hUst γ hγ) (hDst γ hγ), hDst γ hγ⟩
      have hDA : fixV Lk < A := by
        refine lt_of_le_of_ne le_sup_right fun h => ?_
        apply hirr'.1.2.2.2.1.ne
        rw [hfixC]
        exact le_antisymm inf_le_left (le_inf le_rfl (le_sup_left.trans h.symm.le))
      have hirrA := B5.isIrrSec_autSec hDA (fun J hJ hDJ hJA => by
          have hJU := hirr'.1.2.2.2.2 (J ⊓ U) (fun a l hl => by
              have ha : (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈ Lk := hMp ▸ a.2
              exact ⟨hJ _ ha l hl.1, hUinv _ ha l hl.2⟩)
            (by rw [hfixC]; exact fun w hw => ⟨hDJ hw.2, hw.1⟩) inf_le_right
          rw [hfixC] at hJU
          rcases hJU with h | h
          · left
            refine le_antisymm (fun w hw => ?_) hDJ
            obtain ⟨u, hu, d, hd, rfl⟩ := Subgroup.mem_sup.mp (hJA hw)
            have huJ : u ∈ J := by
              have := J.mul_mem hw (J.inv_mem (hDJ hd))
              simpa using this
            have hu' : u ∈ J ⊓ U := ⟨huJ, hu⟩
            rw [h] at hu'
            exact (fixV Lk).mul_mem hu'.2 hd
          · right
            refine le_antisymm hJA (sup_le (fun u hu => ?_) hDJ)
            have hu' : u ∈ J ⊓ U := by rw [h]; exact hu
            exact hu'.1)
        (fun γ hγ => (hLA hγ).1) (fun γ hγ => (hLA hγ).2)
      obtain ⟨γ, hγ, v, hv, hγv⟩ := hnt
      have hnc := nonabelian_autSec hLA (autIH_perfect hF hK₀)
        ⟨γ, hγ, v, Subgroup.mem_sup_left hv, hγv⟩
      exact false_of_sec_cube hW2 hLA hirrA hnc hy3 (fun v _ => hcube v) hyL hrL hr2 hry
        ⟨hyA, hyD⟩ ⟨hrA, hrD⟩
  rintro g ⟨hgI, hgx⟩
  have hgIH : g ∈ conjClosure I H := le_conjClosure I H hgI
  have hgx' : x⁻¹ * g * x ∈ I := mem_conjSub.mp hgx
  have hgxIH : x⁻¹ * g * x ∈ conjClosure I H := le_conjClosure I H hgx'
  have hgm : modMk hIHN g hgIH ∈ U ⊓ Ux := by
    refine ⟨(modMk_mem_subM_iff hIHN hV₁I hgIH).mpr hgI,
      modMk hIHN (x⁻¹ * g * x) hgxIH, (modMk_mem_subM_iff hIHN hV₁I hgxIH).mpr hgx', ?_⟩
    show ψ ⟨x, hxH⟩ (modMk hIHN (x⁻¹ * g * x) hgxIH) = modMk hIHN g hgIH
    rw [actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ hgxIH]
    apply Subtype.ext
    show secMk _ _ ⟨x * (x⁻¹ * g * x) * x⁻¹, _⟩ = secMk _ _ ⟨g, _⟩
    congr 2
    group
  have hD := hmain hgm
  refine ⟨hgI, hIHN hgIH, fun k hk => ?_⟩
  have hkL : ψ ⟨k, hKH hk⟩ ∈ Lk := by
    rw [hLk, autIH_eq_map hF hKH]
    exact ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have h1 := congrArg (fun w : ↥(tildeOf V₁ (conjClosure I H)) =>
    (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) (hD _ hkL)
  rw [actH_apply_coe] at h1
  refine commutator_mem_of_secMk_commute (x := ⟨g, hIHN hgIH⟩)
    (y := ⟨k, hF.H_le_normalizer_V₁ (hKH hk)⟩) ?_
  have h2 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨k, hF.H_le_normalizer_V₁ (hKH hk)⟩ *
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨g, hIHN hgIH⟩ =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨g, hIHN hgIH⟩ *
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨k, hF.H_le_normalizer_V₁ (hKH hk)⟩ := by
    have h3 := congrArg (· * secMk (Subgroup.normalizer (V₁ : Set G)) V₁
      ⟨k, hF.H_le_normalizer_V₁ (hKH hk)⟩) h1
    simp only [inv_mul_cancel_right] at h3
    exact h3
  exact h2.symm

end CFSG.Quasithin.H13.A6.A6S20
