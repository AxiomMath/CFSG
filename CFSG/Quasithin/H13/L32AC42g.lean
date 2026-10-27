module

public import CFSG.Quasithin.H13.L32AC42f

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace TopW

variable {W : Subgroup G} (D : TopW T L V H W) [IsMulCommutative ↥(conjClosure V H)]

theorem map_eq_of_comm {K : Subgroup G} {Vs Wt : Subgroup (Hat V H W)}
    (hVinv : ∀ k ∈ D.autOf K, ∀ v ∈ Vs, k v ∈ Vs) (hWinv : ∀ k ∈ D.autOf K, ∀ v ∈ Wt, k v ∈ Wt)
    (hirr : ∀ J ≤ Vs, (∀ k ∈ D.autOf K, ∀ v ∈ J, k v ∈ J) → J = ⊥ ∨ J = Vs)
    (hcard : Nat.card Vs = Nat.card Wt) (hsup : Vs ⊔ Wt = ⊤) (hinf : Vs ⊓ Wt = ⊥)
    (hiso : ¬ SecIsoL (D.autOf K) Vs ⊥ Wt ⊥) {g : MulAut (Hat V H W)}
    (hgc : ∀ k ∈ D.autOf K, g * k = k * g) : Vs.map g.toMonoidHom = Vs := by
  classical
  set D' := Vs.map g.toMonoidHom with hD'
  have hD'inv : ∀ k ∈ D.autOf K, ∀ v ∈ D', k v ∈ D' := by
    rintro k hk _ ⟨v, hv, rfl⟩
    refine ⟨k v, hVinv k hk v hv, ?_⟩
    show g (k v) = k (g v)
    rw [← MulAut.mul_apply, hgc k hk, MulAut.mul_apply]
  have hD'card : Nat.card D' = Nat.card Vs := Subgroup.card_map_of_injective g.injective
  have hD'irr : ∀ J ≤ D', (∀ k ∈ D.autOf K, ∀ v ∈ J, k v ∈ J) → J = ⊥ ∨ J = D' := by
    intro J hJ hJk
    have hJ' : J.map g⁻¹.toMonoidHom ≤ Vs := by
      rintro _ ⟨j, hj, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hJ hj
      simpa using hv
    rcases hirr _ hJ' (by
      rintro k hk _ ⟨j, hj, rfl⟩
      refine ⟨k j, hJk k hk j hj, ?_⟩
      show g⁻¹ (k j) = k (g⁻¹ j)
      have : g⁻¹ * k = k * g⁻¹ := by
        calc g⁻¹ * k = g⁻¹ * (k * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * k) * g⁻¹ := by rw [hgc k hk]
          _ = k * g⁻¹ := by group
      rw [← MulAut.mul_apply, this, MulAut.mul_apply]) with h0 | h1
    · left
      rw [eq_bot_iff]
      intro j hj
      have : g⁻¹ j ∈ J.map g⁻¹.toMonoidHom := ⟨j, hj, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      simpa using congrArg g this
    · right
      refine le_antisymm hJ fun d hd => ?_
      obtain ⟨v, hv, rfl⟩ := hd
      rw [← h1] at hv
      obtain ⟨j, hj, hjv⟩ := hv
      have : (g.toMonoidHom) v = j := by
        rw [← hjv]
        simp
      rw [this]
      exact hj
  by_cases hmeet : D' ⊓ Vs = ⊥
  · exfalso
    apply hiso
    let e : ↥Vs × ↥Wt →* Hat V H W :=
      MonoidHom.noncommCoprod Vs.subtype Wt.subtype fun a b => mul_comm _ _
    have he : Function.Bijective e := by
      refine ⟨(injective_iff_map_eq_one e).mpr fun ⟨a, b⟩ h => ?_, fun m => ?_⟩
      · have h1 : (a : Hat V H W) * b = 1 := h
        have ha : (a : Hat V H W) ∈ Vs ⊓ Wt := ⟨a.2, by
          rw [eq_inv_of_mul_eq_one_left h1]
          exact Wt.inv_mem b.2⟩
        rw [hinf, Subgroup.mem_bot] at ha
        have hb : (b : Hat V H W) = 1 := by rw [ha, one_mul] at h1; exact h1
        exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
      · obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp (hsup ▸ Subgroup.mem_top m)
        exact ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩
    set E := MulEquiv.ofBijective e he with hE
    have hEsymm : ∀ (a : ↥Vs) (b : ↥Wt), E.symm ((a : Hat V H W) * b) = (a, b) := fun a b =>
      E.symm_apply_eq.mpr rfl
    set p : Hat V H W →* ↥Wt := (MonoidHom.snd _ _).comp E.symm.toMonoidHom with hp
    have hpab : ∀ (a : ↥Vs) (b : ↥Wt), p ((a : Hat V H W) * b) = b := fun a b => by
      show (E.symm ((a : Hat V H W) * b)).2 = b
      rw [hEsymm]
    have hdec : ∀ m : Hat V H W, ∃ (a : ↥Vs) (b : ↥Wt), m = a * b := fun m => by
      obtain ⟨⟨a, b⟩, hab⟩ := he.2 m
      exact ⟨a, b, hab.symm⟩
    let φ : ↥Vs →* ↥Wt := p.comp ((g.toMonoidHom).comp Vs.subtype)
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro v hv
      obtain ⟨a, b, hab⟩ := hdec (g v)
      have hb : b = 1 := by
        have : p (g v) = b := by rw [hab, hpab]
        rw [← this]
        exact hv
      rw [hb, OneMemClass.coe_one, mul_one] at hab
      have hmem : g v ∈ D' ⊓ Vs := ⟨⟨v, v.2, rfl⟩, hab ▸ a.2⟩
      rw [hmeet, Subgroup.mem_bot] at hmem
      exact Subtype.ext (g.injective (hmem.trans (map_one g).symm))
    have hφbij : Function.Bijective φ :=
      (Nat.bijective_iff_injective_and_card φ).mpr ⟨hφinj, hcard⟩
    have hpk : ∀ k ∈ D.autOf K, ∀ m : Hat V H W, ((p (k m) : ↥Wt) : Hat V H W) = k (p m) := by
      intro k hk m
      obtain ⟨a, b, rfl⟩ := hdec m
      rw [hpab a b]
      have : k ((a : Hat V H W) * b) = ((⟨k a, hVinv k hk a a.2⟩ : ↥Vs) : Hat V H W) *
          ((⟨k b, hWinv k hk b b.2⟩ : ↥Wt) : Hat V H W) := map_mul k _ _
      rw [this, hpab]
    refine B5.secIsoL_of_iso (fun a v hv => hVinv a a.2 v hv) (fun a v hv => hWinv a a.2 v hv)
      ⟨MulEquiv.ofBijective φ hφbij, fun a l l' hll' => ?_⟩
    have h1 : (a : MulAut (Hat V H W)) l = l' := hll'
    show (a : MulAut (Hat V H W)) (p (g l)) = p (g l')
    rw [← hpk a a.2, ← MulAut.mul_apply, ← hgc a a.2, MulAut.mul_apply, h1]
  ·
    rcases hD'irr _ inf_le_left (fun k hk v hv => ⟨hD'inv k hk v hv.1, hVinv k hk v hv.2⟩) with
      h0 | h1
    · exact absurd h0 hmeet
    · have hle : D' ≤ Vs := h1.symm.le.trans inf_le_right
      exact Subgroup.eq_of_le_of_card_ge hle hD'card.symm.le

end TopW

namespace Top42

variable {K I : Subgroup G} (C : Top42 T L V H K I) (D : TopW T L V H I)
include C D

variable [IsMulCommutative ↥(conjClosure V H)]

theorem not_d310Two (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    {x t : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V)) (hx1 : x ≠ 1)
    (ht : t ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    (htx : t * x * t⁻¹ = x⁻¹) {Vs : Subgroup (Hat V H I)} (hVs : Vs ∈ IrrPlus (D.autOf K) ⊤) :
    ¬ D310Two (D.autOf T) (D.autOf K) Vs := by
  rintro ⟨-, ⟨t₀, ht₀T, ht₀⟩, hsum⟩
  obtain ⟨hs, hiso⟩ := hsum t₀ ht₀T ht₀
  have hfix := C.fixV_autOf_K D
  rw [hfix, inf_bot_eq, inf_bot_eq] at hiso
  rw [hfix] at hs
  obtain ⟨hs1, hs2⟩ := hs
  simp only [sup_bot_eq] at hs1 hs2
  obtain ⟨hinv, -, hlt, hirr0⟩ := mem_irrPlus_top_iff.mp hVs
  rw [hfix, inf_bot_eq] at hlt hirr0
  have hVs0 : Vs ≠ ⊥ := fun h => (lt_irrefl _ (h ▸ hlt)).elim
  have hirr : ∀ J ≤ Vs, (∀ k ∈ D.autOf K, ∀ v ∈ J, k v ∈ J) → J = ⊥ ∨ J = Vs :=
    fun J hJ hJk => hirr0 J hJk bot_le hJ
  have hWinv : ∀ k ∈ D.autOf K, ∀ w ∈ Vs.map t₀.toMonoidHom, k w ∈ Vs.map t₀.toMonoidHom := by
    rintro k hk _ ⟨v, hv, rfl⟩
    have hk' : t₀⁻¹ * k * t₀ ∈ D.autOf K := by
      have := (Subgroup.mem_normalizer_iff.mp
        (D.autOf_T_le_normalizer C.hKH C.hKn ((D.autOf T).inv_mem ht₀T)) k).mp hk
      simpa using this
    refine ⟨(t₀⁻¹ * k * t₀) v, hinv _ hk' v hv, ?_⟩
    show t₀ ((t₀⁻¹ * k * t₀) v) = k (t₀ v)
    simp [MulAut.mul_apply]
  have hcard : Nat.card Vs = Nat.card (Vs.map t₀.toMonoidHom) :=
    (Subgroup.card_map_of_injective t₀.injective).symm
  have hmap := fun (g : MulAut (Hat V H I)) (hg : ∀ k ∈ D.autOf K, g * k = k * g) =>
    D.map_eq_of_comm hinv hWinv hirr hcard hs1.symm (le_bot_iff.mp hs2) hiso hg
  have hxV := hmap _ fun k hk => D.actS_comm (C.hc hx) hk
  have htV := hmap _ fun k hk => D.actS_comm ht hk
  have hx3 := C.pow_three_of_mem h1222 h1332 h1334 hx
  have ht2 : D.actS t * D.actS t = 1 := by
    rw [← map_mul, sq_eq_one_of_inv hx3 hx1 htx ht fun r hr =>
      C.mem_cent_cases h28 h1222 h1332 h1334 hLie hx hx1 ht htx hr, map_one]
  have htf := D.fix_of_comm_irr hinv hirr hVs0 ht2 (fun k hk => D.actS_comm ht hk)
    (fun v hv => htV ▸ (⟨v, hv, rfl⟩ : D.actS t v ∈ Vs.map (D.actS t).toMonoidHom))
  apply hVs0
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  set a := D.actS x with ha
  set b := D.actS t with hb
  have hav : a v ∈ Vs := hxV ▸ (⟨v, hv, rfl⟩ : a v ∈ Vs.map a.toMonoidHom)
  have hbinv : b⁻¹ = b := (eq_inv_of_mul_eq_one_left ht2).symm
  have hbab : b * a * b⁻¹ = a⁻¹ := by rw [hb, ha, ← map_inv, ← map_mul, ← map_mul, htx, map_inv]
  have h1 : a⁻¹ v = a v := by
    rw [← hbab, MulAut.mul_apply, MulAut.mul_apply, hbinv, htf v hv, htf _ hav]
  have h2 : a (a v) = v := by
    have := congrArg a h1
    rwa [MulAut.apply_inv_self, eq_comm] at this
  have h3 : a (a (a v)) = v := by
    have h3' : a ^ 3 = 1 := by rw [ha, ← map_pow, hx3, map_one]
    have := congrArg (fun φ : MulAut (Hat V H I) => φ v) h3'
    simpa [pow_succ, MulAut.mul_apply] using this
  rw [h2] at h3
  exact C.fix_actS_eq_one D h1222 h1332 h1334 h5 hx hx1 h3

end Top42

end CFSG.Quasithin.H13.L32A.C
