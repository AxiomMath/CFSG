module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CLinkUse
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCaseAA
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CQA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_pair_facts {D : Data G} {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) :
    L ≤ conjClosure D.M L ∧ K ≤ conjClosure D.M L ∧
      conjClosure D.M L ≤ normalizer (L : Set G) ∧
      conjClosure D.M L ≤ normalizer (K : Set G) := by
  have hXsup : conjClosure D.M L = L ⊔ K := conjClosure_eq_sup_of_conjSetOf_eq hset
  have hLX : L ≤ conjClosure D.M L := by rw [hXsup]; exact le_sup_left
  have hKX : K ≤ conjClosure D.M L := by rw [hXsup]; exact le_sup_right
  have hLXn : conjClosure D.M L ≤ normalizer (L : Set G) := by
    rw [hXsup]
    exact sup_le Subgroup.le_normalizer (calC_le_normalizer_of_ne hL hKC hKne.symm)
  have hKXn : conjClosure D.M L ≤ normalizer (K : Set G) := by
    rw [hXsup]
    exact sup_le (calC_le_normalizer_of_ne hKC hL hKne) Subgroup.le_normalizer
  exact ⟨hLX, hKX, hLXn, hKXn⟩

theorem uc22r3e5c_card_le_sq_of_le_cartan {X L K : Subgroup G} {C : Subgroup G}
    (hCX : C ≤ X) (hCodd : Odd (Nat.card C))
    (e : Bar2 X ≃* Bar2 L × Bar2 K) {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hCe : (barImage X C).map e.toMonoidHom = DL.prod DK)
    (hDLc : IsCyclic ↥DL) (hDKc : IsCyclic ↥DK) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup G, E ≤ C → IsElemAbelian q E →
      Nat.card E ≤ q ^ 2 := by
  intro q hq _hq2 E hEC hE
  have hEX : E ≤ X := le_trans hEC hCX
  have hEsub : IsElemAbelian q (E.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hE X
  have hinj : ∀ x ∈ E.subgroupOf X,
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) x = 1 → x = 1 := by
    intro x hx h1
    apply uc22r3e5c_eq_one_of_mk_eq_one hCodd (x := x) (hxC := hEC hx)
    exact e.injective (by rw [map_one]; exact h1)
  have hEf : (E.subgroupOf X).map (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) ≤
      DL.prod DK := by
    rw [← hCe, ← Subgroup.map_map]
    exact Subgroup.map_mono (Subgroup.map_mono (Subgroup.subgroupOf_mono X hEC))
  have hcard : Nat.card (E.subgroupOf X) ≤ q ^ 2 :=
    uc22r3e5c_card_le_sq_of_map_le_prod hq hDLc hDKc
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥X))) hinj hEf hEsub
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv] at hcard
  exact hcard

theorem uc22r3e5c_dvd_card_of_map_prod {X L K : Subgroup G} {C : Subgroup G}
    (hCX : C ≤ X) (e : Bar2 X ≃* Bar2 L × Bar2 K) {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hCe : (barImage X C).map e.toMonoidHom = DL.prod DK) {r : ℕ} (hr : r ∣ Nat.card DL) :
    r ∣ Nat.card C := by
  have h1 : r ∣ Nat.card (DL.prod DK) := by
    rw [Nat.card_congr (Subgroup.prodEquiv DL DK).toEquiv, Nat.card_prod]
    exact hr.trans (dvd_mul_right (Nat.card DL) (Nat.card DK))
  have h2 : Nat.card (DL.prod DK) = Nat.card ((barImage X C).map e.toMonoidHom) := by
    rw [hCe]
  have h3 : Nat.card ((barImage X C).map e.toMonoidHom) ∣ Nat.card (barImage X C) :=
    Subgroup.card_map_dvd _ _
  have h4 : Nat.card (barImage X C) ∣ Nat.card C := by
    have hcard : Nat.card (barImage X C) ∣ Nat.card (C.subgroupOf X) :=
      Subgroup.card_map_dvd _ _
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv] at hcard
  exact h1.trans (h2.symm ▸ h3.trans h4)

theorem uc22r3e5c_dvd_card_inf_of_mul {C C₁ C₂ : Subgroup G}
    (hCcomm : IsMulCommutative ↥C) (hC₁ : C₁ ≤ C) (hC₂ : C₂ ≤ C)
    (hCmul : (C : Set G) = (C₁ : Set G) * (C₂ : Set G))
    {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card C) :
    r ∣ Nat.card C₁ ∨ r ∣ Nat.card C₂ := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hxo⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) r hrC
  have hxmem : (x : G) ∈ (C₁ : Set G) * (C₂ : Set G) := by
    rw [← hCmul]; exact x.2
  obtain ⟨c₁, hc₁, c₂, hc₂, hx_eq⟩ := Set.mem_mul.mp hxmem
  have hc₁C : c₁ ∈ C := hC₁ hc₁
  have hc₂C : c₂ ∈ C := hC₂ hc₂
  let : CommGroup ↥C := IsMulCommutative.instCommGroup
  have hcomm_sub : (⟨c₁, hc₁C⟩ : ↥C) * ⟨c₂, hc₂C⟩ = ⟨c₂, hc₂C⟩ * ⟨c₁, hc₁C⟩ := mul_comm _ _
  have hcomm : c₁ * c₂ = c₂ * c₁ := congrArg Subtype.val hcomm_sub
  have hpow1 : c₁ ^ (Nat.card C₁ * Nat.card C₂) = 1 := by
    have h1 : c₁ ^ Nat.card C₁ = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard C₁ hc₁)
    rw [pow_mul, h1, one_pow]
  have hpow2 : c₂ ^ (Nat.card C₁ * Nat.card C₂) = 1 := by
    have h2 : c₂ ^ Nat.card C₂ = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard C₂ hc₂)
    rw [Nat.mul_comm, pow_mul, h2, one_pow]
  have hpow : (c₁ * c₂) ^ (Nat.card C₁ * Nat.card C₂) = 1 := by
    have hc : Commute c₁ c₂ := (commute_iff_eq c₁ c₂).mpr hcomm
    rw [hc.mul_pow, hpow1, hpow2, one_mul]
  have horder : orderOf (c₁ * c₂) = r := by
    rw [hx_eq, Subgroup.orderOf_coe, hxo]
  have hord : orderOf (c₁ * c₂) ∣ Nat.card C₁ * Nat.card C₂ :=
    orderOf_dvd_of_pow_eq_one hpow
  rw [horder] at hord
  exact hr.dvd_mul.mp hord

private theorem uc22r3e5c_projector_aux {X L K : Subgroup G}
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hLX : L ≤ X) (hKX : K ≤ X)
    (e : Bar2 X ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥X) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥X) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {b : G} (hbXn : b ∈ normalizer (X : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer (K : Set G))
    {eL eK : ℕ}
    (hαL : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ eL)
    (hαK : ∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d = d ^ eK)
    {a : G} (haX : a ∈ X) {z : Bar2 L × Bar2 K}
    (hz : z = e (QuotientGroup.mk ⟨a, haX⟩))
    (hzL : z.1 ∈ DL) (hzK : z.2 ∈ DK)
    (a' : ↥X) (ha' : (a' : G) = b * a * b⁻¹ * (a ^ eK)⁻¹) :
    e (QuotientGroup.mk a') = (z.1 ^ eL * (z.1 ^ eK)⁻¹, 1) := by
  have hlink := uc22r3e5c_link_conj hLX hKX e heL heK hbXn hbL hbK
    (QuotientGroup.mk ⟨a, haX⟩)
  have hb'X : b * a * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hbXn a).mp haX
  have harg : UC6S846.rhoL X ⟨b, hbXn⟩ (QuotientGroup.mk ⟨a, haX⟩) =
      QuotientGroup.mk (⟨b * a * b⁻¹, hb'X⟩ : ↥X) := by
    rw [UC6S846.rhoL_mk]
    rfl
  have h1 : e (QuotientGroup.mk (⟨b * a * b⁻¹, hb'X⟩ : ↥X)) = (z.1 ^ eL, z.2 ^ eK) := by
    rw [← harg, hlink, ← hz]
    exact Prod.ext (hαL z.1 hzL) (hαK z.2 hzK)
  have h2 : e (QuotientGroup.mk (⟨a ^ eK, X.pow_mem haX eK⟩ : ↥X)) =
      (z.1 ^ eK, z.2 ^ eK) := by
    have hsub : (⟨a ^ eK, X.pow_mem haX eK⟩ : ↥X) = ⟨a, haX⟩ ^ eK := by
      ext
      simp [Subgroup.coe_pow]
    rw [hsub, QuotientGroup.mk_pow, map_pow, ← hz]
    rfl
  have hX : b * a * b⁻¹ * (a ^ eK)⁻¹ ∈ X :=
    X.mul_mem hb'X (X.inv_mem (X.pow_mem haX eK))
  have h3 : QuotientGroup.mk a' =
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨b * a * b⁻¹ * (a ^ eK)⁻¹, hX⟩ : ↥X) := by
    congr 1
    exact Subtype.ext ha'
  have h4 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨b * a * b⁻¹ * (a ^ eK)⁻¹, hX⟩ : ↥X) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨b * a * b⁻¹, hb'X⟩ : ↥X) *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨a ^ eK, X.pow_mem haX eK⟩ : ↥X))⁻¹ := by
    have h1' : (⟨b * a * b⁻¹ * (a ^ eK)⁻¹, hX⟩ : ↥X) =
        ⟨b * a * b⁻¹, hb'X⟩ * ⟨a ^ eK, X.pow_mem haX eK⟩⁻¹ := by
      ext
      simp [mul_assoc]
    rw [h1', map_mul, map_inv]
  rw [h3, h4, map_mul, map_inv]
  simp only [QuotientGroup.mk'_apply]
  rw [h1, h2, Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel]

private theorem uc22r3e5c_projector_ne {X L K : Subgroup G}
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hLX : L ≤ X) (hKX : K ≤ X)
    (e : Bar2 X ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥X) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥X) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {b : G} (hbXn : b ∈ normalizer (X : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer (K : Set G))
    {eL eK r : ℕ} (hr : r.Prime) (hreL : (eL : ZMod r) ≠ eK)
    (hαL : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ eL)
    (hαK : ∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d = d ^ eK)
    {a : G} (haX : a ∈ X) {z : Bar2 L × Bar2 K}
    (hz : z = e (QuotientGroup.mk ⟨a, haX⟩))
    (hzL : z.1 ∈ DL) (hzK : z.2 ∈ DK)
    (hz1ord : orderOf z.1 = r) (hz1 : z.1 ≠ 1)
    (a' : ↥X) (ha' : (a' : G) = b * a * b⁻¹ * (a ^ eK)⁻¹) :
    (a' : G) ≠ 1 := by
  intro hone
  have ha'X1 : a' = 1 := Subtype.ext hone
  have hproj := uc22r3e5c_projector_aux hLX hKX e heL heK hbXn hbL hbK hαL hαK
    haX hz hzL hzK a' ha'
  have h1 : z.1 ^ eL * (z.1 ^ eK)⁻¹ = 1 := by
    have := congrArg Prod.fst hproj
    rw [ha'X1, QuotientGroup.mk_one, map_one] at this
    simpa using this.symm
  have h2 : z.1 ^ eL = z.1 ^ eK := mul_inv_eq_one.mp h1
  have hmod : eL ≡ eK [MOD r] := by
    have h := pow_eq_pow_iff_modEq.mp h2
    rwa [hz1ord] at h
  exact hreL ((ZMod.natCast_eq_natCast_iff _ _ _).2 hmod)

private theorem uc22r3e5c_projector_pow {C A : Subgroup G}
    (hAC : A ≤ C) (hCcomm : IsMulCommutative ↥C)
    {a b : G} {eK r : ℕ} (haC : a ∈ C) (haA : a ∈ A)
    (hbA : b ∈ normalizer (A : Set G)) (hao : orderOf a = r)
    (a' : G) (ha' : a' = b * a * b⁻¹ * (a ^ eK)⁻¹) : a' ^ r = 1 := by
  have hbA' : b * a * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hbA a).mp haA
  have hcomm : Commute (b * a * b⁻¹) (a ^ eK)⁻¹ := by
    have hc : Commute (b * a * b⁻¹) a := by
      let : CommGroup ↥C := IsMulCommutative.instCommGroup
      have h1 : (⟨b * a * b⁻¹, hAC hbA'⟩ : ↥C) * ⟨a, haC⟩ =
          ⟨a, haC⟩ * ⟨b * a * b⁻¹, hAC hbA'⟩ := mul_comm _ _
      exact congrArg Subtype.val h1
    exact (hc.pow_right eK).inv_right
  have har : a ^ r = 1 := hao ▸ pow_orderOf_eq_one a
  rw [ha', hcomm.mul_pow, conj_pow, inv_pow, ← pow_mul]
  have h : a ^ (eK * r) = 1 := by rw [Nat.mul_comm eK r, pow_mul, har, one_pow]
  rw [h, inv_one, mul_one]
  simp [har]

private theorem uc22r3e5c_exists_coord_elt_ne_one {X L K C A : Subgroup G}
    (hLX : L ≤ X) (hKX : K ≤ X) (hLXn : X ≤ normalizer (L : Set G))
    (hCX : C ≤ X) (hCodd : Odd (Nat.card C)) (hCcomm : IsMulCommutative ↥C)
    (hAC : A ≤ C)
    (e : Bar2 X ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥X) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥X) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    {b : G} (hbXn : b ∈ normalizer (X : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer (K : Set G)) (hbA : b ∈ normalizer (A : Set G))
    {eL eK r : ℕ} (hr : r.Prime) (hreL : (eL : ZMod r) ≠ eK)
    (hαL : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ eL)
    (hαK : ∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d = d ^ eK)
    {a : G} (haA : a ∈ A) (hao : orderOf a = r) (haX : a ∈ X)
    {z : Bar2 L × Bar2 K} (hz : z = e (QuotientGroup.mk ⟨a, haX⟩))
    (hzL : z.1 ∈ DL) (hzK : z.2 ∈ DK)
    (hz1ord : orderOf z.1 = r) (hz1 : z.1 ≠ 1) :
    ∃ y ∈ A, orderOf y = r ∧ (y ∈ L ∨ y ∈ K) := by
  have haC : a ∈ C := hAC haA
  let a' : G := b * a * b⁻¹ * (a ^ eK)⁻¹
  have hbA' : b * a * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hbA a).mp haA
  have ha'A : a' ∈ A := A.mul_mem hbA' (A.inv_mem (A.pow_mem haA eK))
  have ha'C : a' ∈ C := hAC ha'A
  have ha'X : a' ∈ X := hCX ha'C
  let a'X : ↥X := ⟨a', ha'X⟩
  have hproj : e (QuotientGroup.mk a'X) = (z.1 ^ eL * (z.1 ^ eK)⁻¹, 1) :=
    uc22r3e5c_projector_aux hLX hKX e heL heK hbXn hbL hbK hαL hαK haX
      (z := z) hz hzL hzK a'X (by simp [a'X, a'])
  have ha'snd : (e (QuotientGroup.mk a'X)).2 = 1 := by rw [hproj]
  have hodd' : Nat.Coprime (orderOf a') 2 := by
    have ho : Odd (orderOf a') :=
      Odd.of_dvd_nat hCodd (Subgroup.orderOf_dvd_natCard C ha'C)
    exact Nat.coprime_two_right.mpr ho
  have ha'L : a' ∈ L :=
    uc22r3e5c_link_mem_of_snd_eq_one hLX hLXn e heL (x := a'X) ha'snd hodd'
  have ha'ne : a' ≠ 1 :=
    uc22r3e5c_projector_ne hLX hKX e heL heK hbXn hbL hbK hr hreL hαL hαK
      haX hz hzL hzK hz1ord hz1 a'X (by simp [a'X, a'])
  have ha'pow : a' ^ r = 1 :=
    uc22r3e5c_projector_pow hAC hCcomm haC haA hbA hao a' rfl
  have ha'ord : orderOf a' = r := by
    rcases hr.eq_one_or_self_of_dvd (orderOf a') (orderOf_dvd_of_pow_eq_one ha'pow) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha'ne
    · exact h
  exact ⟨a', ha'A, ha'ord, Or.inl ha'L⟩

private theorem uc22r3e5c_exists_coord_elt_normalizer {X L K : Subgroup G} {C : Subgroup G}
    (hLX : L ≤ X) (hKX : K ≤ X)
    (hLXn : X ≤ normalizer (L : Set G)) (hKXn : X ≤ normalizer (K : Set G))
    (hCX : C ≤ X) (hCodd : Odd (Nat.card C)) (hCcomm : IsMulCommutative ↥C)
    (A : Subgroup G) (hAC : A ≤ C)
    (e : Bar2 X ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥X) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥X) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hCe : (barImage X C).map e.toMonoidHom = DL.prod DK)
    {b : G} (hbXn : b ∈ normalizer (X : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hbK : b ∈ normalizer (K : Set G)) (hbA : b ∈ normalizer (A : Set G))
    {eL eK r : ℕ} (hr : r.Prime) (hreL : (eL : ZMod r) ≠ eK)
    (hαL : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ eL)
    (hαK : ∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d = d ^ eK)
    {a : G} (haA : a ∈ A) (hao : orderOf a = r) :
    ∃ y ∈ A, orderOf y = r ∧ (y ∈ L ∨ y ∈ K) := by
  have haC : a ∈ C := hAC haA
  have haX : a ∈ X := hCX haC
  let aX : ↥X := ⟨a, haX⟩
  let z := e (QuotientGroup.mk aX)
  have hq : QuotientGroup.mk aX ∈ barImage X C := by
    rw [barImage]
    exact Subgroup.mem_map_of_mem _ (by simpa [aX, Subgroup.mem_subgroupOf] using haC)
  have hqa : z ∈ DL.prod DK := by
    have h := Subgroup.mem_map_of_mem e.toMonoidHom hq
    rwa [hCe] at h
  obtain ⟨hzL, hzK⟩ := Subgroup.mem_prod.mp hqa
  have hodd : Nat.Coprime (orderOf a) 2 := by
    have ho : Odd (orderOf a) := Odd.of_dvd_nat hCodd (Subgroup.orderOf_dvd_natCard C haC)
    exact Nat.coprime_two_right.mpr ho
  by_cases hz1 : z.1 = 1
  · exact ⟨a, haA, hao, Or.inr (uc22r3e5c_link_mem_of_fst_eq_one hKX hKXn e heK (x := aX) hz1 hodd)⟩
  · have haXo : orderOf aX = r := (Subgroup.orderOf_coe aX).symm.trans hao
    have hzpow : z ^ r = 1 := by
      rw [show z = e (QuotientGroup.mk aX) from rfl, ← map_pow, ← QuotientGroup.mk_pow,
        ← haXo, pow_orderOf_eq_one, QuotientGroup.mk_one, map_one]
    have hzord : orderOf z = r := by
      rcases hr.eq_one_or_self_of_dvd (orderOf z) (orderOf_dvd_of_pow_eq_one hzpow) with h | h
      · exfalso
        exact hz1 (Prod.ext_iff.mp (orderOf_eq_one_iff.mp h) |>.1)
      · exact h
    have hz1ord : orderOf z.1 = r := by
      have hd : orderOf z.1 ∣ r :=
        (orderOf_map_dvd (MonoidHom.fst (Bar2 L) (Bar2 K)) z).trans (dvd_of_eq hzord)
      rcases hr.eq_one_or_self_of_dvd (orderOf z.1) hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hz1
      · exact h
    exact uc22r3e5c_exists_coord_elt_ne_one (z := z) hLX hKX hLXn hCX hCodd hCcomm hAC e heL heK
      hbXn hbL hbK hbA hr hreL hαL hαK haA hao haX rfl hzL hzK hz1ord hz1

theorem uc22r3e5c_mem_uniqueSet_of_coord {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D) (h1930 : H1930 D)
    (c : Ctx21 D Ch) (he : CFSG.Open.evenRank G = 3) {Y : Subgroup G}
    (hY : Y ∈ calC D.M) (hcY : (conjSetOf D.M Y).ncard = 2) {n : ℕ}
    (hSzY : IsSz (Bar2 Y) n) {r : ℕ} (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1)
    {y : G} (hyY : y ∈ Y) (hyo : orderOf y = r) :
    Subgroup.zpowers y ∈ uniqueSet D.M := by
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hodd : Odd n := uc22r3e5c_odd_of_isSz hSzY
  exact hU2 he Y n n r p hY hcY (h15 h1930 c Y hY hcY n (Or.inl hSzY) p hp)
    hodd dvd_rfl hr hrn hp _ (Subgroup.zpowers_le.2 hyY) (by rw [Nat.card_zpowers, hyo])

private theorem uc22r3e5c_false_of_dvd_inf_cases {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (he : CFSG.Open.evenRank G = 3) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) (hSzK : IsSz (Bar2 K) n)
    {C : Subgroup G} (hCodd : Odd (Nat.card C)) (hCcomm : IsMulCommutative ↥C)
    (hperm : Permutes C D.T) (hCTs : Group.IsSolvable ↥(C ⊔ D.T))
    {r : ℕ} (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1)
    {y : G} (hyA : y ∈ C ⊓ H) (hyo : orderOf y = r) (hyLK : y ∈ L ∨ y ∈ K)
    (hCrk : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup G, E ≤ C → IsElemAbelian q E →
      Nat.card E ≤ q ^ 2)
    (hAp : (Nat.card (Subgroup.zpowers y)).Prime)
    (hA2 : Nat.card (Subgroup.zpowers y) ≠ 2) : False := by
  have hyC : y ∈ C := hyA.1
  have hyH : y ∈ H := hyA.2
  rcases hyLK with hyL | hyK
  · have hcL : (conjSetOf D.M L).ncard = 2 := by
      rw [hset]
      exact Set.ncard_pair hKne.symm
    have hU : Subgroup.zpowers y ∈ uniqueSet D.M :=
      uc22r3e5c_mem_uniqueSet_of_coord hSg h15 hU2 h1930 c he hL hcL hSz hr hrn hyL hyo
    exact uc22r3e5c_false_of_le_hSet h211 h1930 c hH hCodd hCcomm hperm hCTs hCrk
      (Subgroup.zpowers_le.2 hyC) (Subgroup.zpowers_le.2 hyH) hAp hA2 hU
  · have hcK : (conjSetOf D.M K).ncard = 2 := by
      have hmem : K ∈ conjSetOf D.M L := by rw [hset]; simp
      rw [uc22p2214_conjSetOf_eq hmem, hset]
      exact Set.ncard_pair hKne.symm
    have hU : Subgroup.zpowers y ∈ uniqueSet D.M :=
      uc22r3e5c_mem_uniqueSet_of_coord hSg h15 hU2 h1930 c he hKC hcK hSzK hr hrn hyK hyo
    exact uc22r3e5c_false_of_le_hSet h211 h1930 c hH hCodd hCcomm hperm hCTs hCrk
      (Subgroup.zpowers_le.2 hyC) (Subgroup.zpowers_le.2 hyH) hAp hA2 hU

theorem uc22r3e5c_false_of_dvd_inf {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (he : CFSG.Open.evenRank G = 3) {H : Subgroup G}
    (hH : H ∈ hSet D.T D.M) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) (hSzK : IsSz (Bar2 K) n)
    {C : Subgroup G} (hCX : C ≤ conjClosure D.M L) (hCodd : Odd (Nat.card C))
    (hCcomm : IsMulCommutative ↥C) (hperm : Permutes C D.T)
    (hCTs : Group.IsSolvable ↥(C ⊔ D.T)) {b : G}
    (hbC : b ∈ normalizer ((C ⊓ H : Subgroup G) : Set G))
    (e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hCe : (barImage (conjClosure D.M L) C).map e.toMonoidHom = DL.prod DK)
    (hDLc : IsCyclic ↥DL) (hDKc : IsCyclic ↥DK)
    (hbL : b ∈ normalizer (L : Set G)) (hbK : b ∈ normalizer (K : Set G))
    {eL eK r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1)
    (hreL : (eL : ZMod r) ≠ eK)
    (hαL : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ eL)
    (hαK : ∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d = d ^ eK)
    (hrH : r ∣ Nat.card (C ⊓ H : Subgroup G)) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hLX, hKX, hLXn, hKXn⟩ := uc22r3e5c_pair_facts hL hKC hKne hset
  have hbX : b ∈ normalizer (conjClosure D.M L : Set G) := by
    rw [conjClosure_eq_sup_of_conjSetOf_eq hset]
    exact Subgroup.inf_normalizer_le_normalizer_sup L K ⟨hbL, hbK⟩
  obtain ⟨x, hxo⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ H)) r hrH
  have hxC : (x : G) ∈ C := x.2.1
  have hxH : (x : G) ∈ H := x.2.2
  have hao : orderOf (x : G) = r := (Subgroup.orderOf_coe x).trans hxo
  obtain ⟨y, hyA, hyo, hyLK⟩ := uc22r3e5c_exists_coord_elt_normalizer hLX hKX hLXn hKXn hCX hCodd
    hCcomm (C ⊓ H) inf_le_left e heL heK hCe hbX hbL hbK hbC hr hreL hαL hαK
    x.2 hao
  have hyC : y ∈ C := hyA.1
  have hyH : y ∈ H := hyA.2
  have hCrk : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup G, E ≤ C → IsElemAbelian q E →
      Nat.card E ≤ q ^ 2 :=
    uc22r3e5c_card_le_sq_of_le_cartan hCX hCodd e hCe hDLc hDKc
  have hAp : (Nat.card (Subgroup.zpowers y)).Prime := by
    rw [Nat.card_zpowers, hyo]
    exact hr
  have hA2 : Nat.card (Subgroup.zpowers y) ≠ 2 := by
    rw [Nat.card_zpowers, hyo]
    exact hr2
  exact uc22r3e5c_false_of_dvd_inf_cases hSg h15 hU2 h211 h1930 c he hH hL hKC hKne hset
    hSz hSzK hCodd hCcomm hperm hCTs hr hrn hyA hyo hyLK hCrk hAp hA2

private theorem uc22r3e5c_false_of_caseA_branch {D : Data G} {Ch : Choice2011 G}
    {L K : Subgroup G} {C : Subgroup G} {b : G}
    {e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K}
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)} {eL eK r : ℕ} {n : ℕ}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (he : CFSG.Open.evenRank G = 3) (H : Subgroup G)
    (hH : H ∈ hSet D.T D.M)
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) (hSz : IsSz (Bar2 L) n) (hSzK : IsSz (Bar2 K) n)
    (hCX : C ≤ conjClosure D.M L) (hCodd : Odd (Nat.card C))
    (hCcomm : IsMulCommutative ↥C) (hperm : Permutes C D.T)
    (hCTs : Group.IsSolvable ↥(C ⊔ D.T)) (hbC : b ∈ normalizer ((C ⊓ H : Subgroup G) : Set G))
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    (hCe : (barImage (conjClosure D.M L) C).map e.toMonoidHom = DL.prod DK)
    (hDLc : IsCyclic ↥DL) (hDKc : IsCyclic ↥DK)
    (hbL : b ∈ normalizer (L : Set G)) (hbK : b ∈ normalizer (K : Set G))
    (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1)
    (hreL : (eL : ZMod r) ≠ eK)
    (hαL : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ eL)
    (hαK : ∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d = d ^ eK)
    (hrH : r ∣ Nat.card (C ⊓ H : Subgroup G)) : False :=
  uc22r3e5c_false_of_dvd_inf (D := D) (Ch := Ch) (H := H) (L := L) (K := K)
    (C := C) (b := b) (DL := DL) (DK := DK) (eL := eL) (eK := eK) (r := r)
    (hSg := hSg) (h15 := h15) (hU2 := hU2) (h211 := h211) (h1930 := h1930)
    (c := c) (he := he) (hH := hH) (hL := hL) (hKC := hKC) (hKne := hKne)
    (hset := hset) (hSz := hSz) (hSzK := hSzK) (hCX := hCX) (hCodd := hCodd)
    (hCcomm := hCcomm) (hperm := hperm) (hCTs := hCTs) (hbC := hbC)
    (e := e) (heL := heL) (heK := heK) (hCe := hCe) (hDLc := hDLc)
    (hDKc := hDKc) (hbL := hbL) (hbK := hbK) (hr := hr) (hr2 := hr2)
    (hrn := hrn) (hreL := hreL) (hαL := hαL) (hαK := hαK) (hrH := hrH)

theorem uc22r3e5c_false_of_caseA {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (he : CFSG.Open.evenRank G = 3) {H₁ H₂ : Subgroup G}
    (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2)
    (hKne : K ≠ L) (hset : conjSetOf D.M L = {L, K}) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) (hSzK : IsSz (Bar2 K) n)
    {C : Subgroup G} (hCX : C ≤ conjClosure D.M L) (hCodd : Odd (Nat.card C))
    (hCcomm : IsMulCommutative ↥C) (hperm : Permutes C D.T)
    (hCTs : Group.IsSolvable ↥(C ⊔ D.T)) {b : G}
    (hbC₁ : b ∈ normalizer ((C ⊓ H₁ : Subgroup G) : Set G))
    (hbC₂ : b ∈ normalizer ((C ⊓ H₂ : Subgroup G) : Set G))
    (hCmul : (C : Set G) = ((C ⊓ H₁ : Subgroup G) : Set G) * ((C ⊓ H₂ : Subgroup G) : Set G))
    (e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K)
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K)))
    {DL : Subgroup (Bar2 L)} {DK : Subgroup (Bar2 K)}
    (hCe : (barImage (conjClosure D.M L) C).map e.toMonoidHom = DL.prod DK)
    (hDLc : IsCyclic ↥DL) (hDKc : IsCyclic ↥DK) (hDLcard : Nat.card DL = 2 ^ n - 1)
    (hbL : b ∈ normalizer (L : Set G)) (hbK : b ∈ normalizer (K : Set G))
    {eL eK r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1)
    (hreL : (eL : ZMod r) ≠ eK)
    (hαL : ∀ d ∈ DL, UC6S846.rhoL L ⟨b, hbL⟩ d = d ^ eL)
    (hαK : ∀ d ∈ DK, UC6S846.rhoL K ⟨b, hbK⟩ d = d ^ eK) : False := by
  have hDLdvd : r ∣ Nat.card DL := by rwa [hDLcard]
  have hrC : r ∣ Nat.card C :=
    uc22r3e5c_dvd_card_of_map_prod (X := conjClosure D.M L) (L := L) (K := K) (C := C)
      (DL := DL) (DK := DK) (r := r) hCX e hCe hDLdvd
  have hdiv : r ∣ Nat.card (C ⊓ H₁ : Subgroup G) ∨ r ∣ Nat.card (C ⊓ H₂ : Subgroup G) :=
    uc22r3e5c_dvd_card_inf_of_mul (C := C) (C₁ := C ⊓ H₁) (C₂ := C ⊓ H₂)
      hCcomm inf_le_left inf_le_left hCmul hr hrC
  rcases hdiv with h1 | h2
  · exact uc22r3e5c_false_of_caseA_branch hSg h15 hU2 h211 h1930 c he H₁ hH₁ hL hKC hKne
      hset hSz hSzK hCX hCodd hCcomm hperm hCTs hbC₁ heL heK hCe hDLc hDKc hbL hbK
      hr hr2 hrn hreL hαL hαK h1
  · exact uc22r3e5c_false_of_caseA_branch hSg h15 hU2 h211 h1930 c he H₂ hH₂ hL hKC hKne
      hset hSz hSzK hCX hCodd hCcomm hperm hCTs hbC₂ heL heK hCe hDLc hDKc hbL hbK
      hr hr2 hrn hreL hαL hαK h2
end CFSG.LocalAnalysis.UniquenessCase.UC22
