module

public import CFSG.Quasithin.Background.SmithB45M22HatLocal
public import CFSG.Quasithin.Background.SmithB45M22HatM22
public import CFSG.Quasithin.Background.SmithB45Families
public import CFSG.Quasithin.Background.SmithB45ExcEngine
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.EmptyFaithful.A38c14CentralLift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42DichProof
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22

public section

namespace CFSG.Quasithin.HatM22

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Quasithin.A38c14

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem pow_three_of_mem_center {L : Subgroup (MulAut V)}
    (hZ3 : Nat.card (Subgroup.center ↥L) = 3) {c : ↥L} (hc : c ∈ Subgroup.center ↥L) :
    c ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥L)) (x := ⟨c, hc⟩)
  rw [hZ3] at h
  have h' := congrArg Subtype.val h
  rwa [SubgroupClass.coe_pow] at h'

omit [Finite V] in
theorem fixV_center_eq_bot {L : Subgroup (MulAut V)} (hirr : IsIrrOn L) {c : ↥L}
    (hc : c ∈ Subgroup.center ↥L) (hc1 : c ≠ 1) :
    fixV (Subgroup.zpowers (c : MulAut V)) = ⊥ := by
  rcases hirr.2 (fixV (Subgroup.zpowers (c : MulAut V))) (by
    intro g hg u hu
    rw [mem_fixV_zpowers_iff] at hu ⊢
    have hcg : (c : MulAut V) * g = g * (c : MulAut V) :=
      (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨g, hg⟩)).symm
    calc (c : MulAut V) (g u) = ((c : MulAut V) * g) u := rfl
      _ = (g * (c : MulAut V)) u := by rw [hcg]
      _ = g u := by rw [MulAut.mul_apply, hu]) with h | h
  · exact h
  · exfalso
    apply hc1
    apply Subtype.ext
    ext v
    have hv : v ∈ fixV (Subgroup.zpowers (c : MulAut V)) := h ▸ Subgroup.mem_top v
    exact mem_fixV_zpowers_iff.1 hv

omit [Finite V] in
theorem card_hatL {L : Subgroup (MulAut V)}
    (hZ3 : Nat.card (Subgroup.center ↥L) = 3) (e : CQ L ≃* ↥NativeSporadic.M22) :
    Nat.card ↥L = 3 ^ 3 * 49280 := by
  have h1 := Subgroup.card_mul_index (Subgroup.center ↥L)
  rw [Subgroup.index, Nat.card_congr e.toEquiv, card_M22, hZ3] at h1
  rw [← h1]
  norm_num

omit [Finite V] in
theorem exists_partner_lift
    {L : Subgroup (MulAut V)} (hZ3 : Nat.card (Subgroup.center ↥L) = 3)
    (e : CQ L ≃* ↥NativeSporadic.M22) {t : ↥L} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ s : ↥L, s * s = 1 ∧ (t * s) ^ 3 = 1 ∧ t * s ∉ Subgroup.center ↥L := by
  have hcube : ∀ c ∈ Subgroup.center ↥L, c ^ 3 = 1 := fun c hc => pow_three_of_mem_center hZ3 hc
  have htc : t ∉ Subgroup.center ↥L := by
    intro h
    apply ht1
    have h3 := hcube t h
    calc t = t ^ 3 * (t * t)⁻¹ := by group
      _ = 1 := by rw [h3, ht, inv_one, one_mul]
  set tb := redHom L e t
  have htb1 : tb ≠ 1 := fun h => htc ((redHom_eq_one_iff L e t).1 h)
  have htb2 : tb ^ 2 = 1 := by rw [sq, ← map_mul, ht, map_one]
  have ho : orderOf (tb : Equiv.Perm (Fin 22)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime htb2 htb1
  obtain ⟨v, hv, hvv, hcube', hne⟩ := m22_exists_partner tb.2 ho
  obtain ⟨s₀, hs₀⟩ := redHom_surjective L e ⟨v, hv⟩
  have hs₀sq : s₀ * s₀ ∈ Subgroup.center ↥L := by
    rw [← redHom_eq_one_iff L e, map_mul, hs₀]
    exact Subtype.ext hvv
  have hs6 : s₀ ^ 3 * s₀ ^ 3 = (s₀ * s₀) ^ 3 := by rw [← pow_add, ← sq, ← pow_mul]
  refine ⟨s₀ ^ 3, ?_, ?_, ?_⟩
  · rw [hs6]
    exact hcube _ hs₀sq
  ·
    set s := s₀ ^ 3 with hs
    have hrs : redHom L e s = ⟨v, hv⟩ := by
      rw [hs, map_pow, hs₀]
      apply Subtype.ext
      rw [SubgroupClass.coe_pow]
      rw [pow_succ, sq, hvv, one_mul]
    have hss : s * s = 1 := by
      rw [hs, hs6]
      exact hcube _ hs₀sq
    have hwc : (t * s) ^ 3 ∈ Subgroup.center ↥L := by
      rw [← redHom_eq_one_iff L e, map_pow, map_mul, hrs]
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, Subgroup.coe_mul]
      exact hcube'
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hconj1 : t * (t * s) * t⁻¹ = (t * s)⁻¹ := by
      rw [mul_inv_rev, hti, hsi, ← mul_assoc, ht, one_mul]
    have hinv : t * (t * s) ^ 3 * t⁻¹ = ((t * s) ^ 3)⁻¹ := by
      rw [← conj_pow, hconj1, inv_pow]
    have hcomm : t * (t * s) ^ 3 * t⁻¹ = (t * s) ^ 3 := by
      rw [Subgroup.mem_center_iff.1 hwc t, mul_inv_cancel_right]
    have hw2 : (t * s) ^ 3 * (t * s) ^ 3 = 1 := by
      have h' : (t * s) ^ 3 = ((t * s) ^ 3)⁻¹ := hcomm.symm.trans hinv
      calc (t * s) ^ 3 * (t * s) ^ 3 = (t * s) ^ 3 * ((t * s) ^ 3)⁻¹ := by rw [← h']
        _ = 1 := mul_inv_cancel _
    have hw3 := hcube _ hwc
    calc (t * s) ^ 3 = ((t * s) ^ 3) ^ 3 * ((t * s) ^ 3 * (t * s) ^ 3)⁻¹ := by group
      _ = 1 := by rw [hw3, hw2, inv_one, one_mul]
  · intro h
    apply hne
    have h1 := (redHom_eq_one_iff L e (t * s₀ ^ 3)).2 h
    rw [map_mul, map_pow, hs₀] at h1
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, SubgroupClass.coe_pow] at h2
    calc (tb : Equiv.Perm (Fin 22)) * v = (tb : Equiv.Perm (Fin 22)) * v ^ 3 := by
          rw [pow_succ, sq, hvv, one_mul]
      _ = 1 := h2

theorem comm_of_card_27 {R : Type*} [Group R] [Finite R] (hR : Nat.card R = 3 ^ 3)
    (h4 : 4 ≤ Nat.card (Subgroup.center R)) (a b : R) : a * b = b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 R := IsPGroup.of_card hR
  obtain ⟨k, hk⟩ := (hp.to_subgroup (Subgroup.center R)).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> rw [hk] at h4 <;> norm_num at h4
  have hm := Subgroup.card_mul_index (Subgroup.center R)
  rw [hk, hR] at hm
  have h9 : 3 ^ k = 3 ^ 2 * 3 ^ (k - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h9, mul_assoc] at hm
  have h3 : 3 ^ (k - 2) * (Subgroup.center R).index = 3 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3 ^ 2) (hm.trans (by norm_num))
  have hidx : (Subgroup.center R).index ∣ 3 := Dvd.intro_left _ h3
  have hcyc : IsCyclic (R ⧸ Subgroup.center R) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hidx with h | h
    · rw [Subgroup.index_eq_card] at h
      have hs : Subsingleton (R ⧸ Subgroup.center R) := (Nat.card_eq_one_iff_unique.1 h).1
      exact isCyclic_of_subsingleton
    · rw [Subgroup.index_eq_card] at h
      exact isCyclic_of_prime_card (p := 3) h
  have := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (Subgroup.center R)) (by rw [QuotientGroup.ker_mk'])
  exact this.is_comm.comm a b

theorem exists_conj_mul_center {L : Subgroup (MulAut V)}
    (hZ3 : Nat.card (Subgroup.center ↥L) = 3) (hperf : Group.IsPerfect ↥L)
    (e : CQ L ≃* ↥NativeSporadic.M22) {y : ↥L} (hy : y ^ 3 = 1)
    (hyc : y ∉ Subgroup.center ↥L) :
    ∃ x : ↥L, ∃ c ∈ Subgroup.center ↥L, c ≠ 1 ∧ x⁻¹ * y * x = y * c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLcard := card_hatL hZ3 e
  have hkerc : (redHom L e).ker = Subgroup.center ↥L := by
    ext g
    rw [MonoidHom.mem_ker, redHom_eq_one_iff]
  obtain ⟨⟨z, hzC⟩, hz3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 3
    (dvd_of_eq hZ3.symm)
  rw [Subgroup.orderOf_mk] at hz3
  have hy1 : y ≠ 1 := fun h => hyc (h ▸ one_mem _)
  have hyp : IsPGroup 3 (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers]
    have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · rw [h, pow_one]
  obtain ⟨R, hyR⟩ := hyp.exists_le_sylow
  have hyR' : y ∈ R := hyR (Subgroup.mem_zpowers y)
  have hRcard : Nat.card R = 3 ^ 3 := card_sylow_three R (m := 49280) (by norm_num) hLcard
  have hzR : z ∈ R := mem_sylow_three_of_central R hzC hz3
  have hzpow : Subgroup.zpowers z = Subgroup.center ↥L := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzC) ?_
    rw [Nat.card_zpowers, hz3, hZ3]
  have hcenterR : Subgroup.center ↥L ≤ (R : Subgroup ↥L) := by
    rw [← hzpow]
    exact Subgroup.zpowers_le.mpr hzR
  have hRna : ¬ ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro hab
    have hzc : z ∈ commutator ↥L := by
      rw [(Group.isPerfect_def).1 hperf]
      exact Subgroup.mem_top z
    have := central_mem_commutator_eq_one_of_abelian_sylow R hab hzC hzR hzc
    rw [this, orderOf_one] at hz3
    norm_num at hz3
  have hex : ∃ x ∈ R, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hRna
    intro a ha b hb
    let Rs : Subgroup ↥L := R
    have hyZ : (⟨y, hyR'⟩ : ↥Rs) ∈ Subgroup.center ↥Rs := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcon g g.2)
    have hZZ : ∀ (c : ↥L) (hc : c ∈ Subgroup.center ↥L),
        (⟨c, hcenterR hc⟩ : ↥Rs) ∈ Subgroup.center ↥Rs := by
      intro c hc
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.1 hc g)
    have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz3; norm_num at hz3
    have hzz : z ≠ z ^ 2 := fun h => hz1 (by
      calc z = z ^ 2 * z⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel])
    have hz21 : z ^ 2 ≠ 1 := fun h => hz1 (by
      calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
        _ = 1 := by rw [h, inv_one, mul_one, ← hz3, pow_orderOf_eq_one])
    have hyz : y ≠ z := fun h => hyc (h ▸ hzC)
    have hyz2 : y ≠ z ^ 2 := fun h => hyc (h ▸ Subgroup.pow_mem _ hzC 2)
    have h4 : 4 ≤ Nat.card (Subgroup.center ↥Rs) := by
      let f : Fin 4 → ↥(Subgroup.center ↥Rs) := ![1, ⟨⟨z, hzR⟩, hZZ z hzC⟩,
        ⟨⟨z ^ 2, R.pow_mem hzR 2⟩, hZZ _ (Subgroup.pow_mem _ hzC 2)⟩, ⟨⟨y, hyR'⟩, hyZ⟩]
      have hf : Function.Injective f := by
        intro i j hij
        have hv := congrArg (fun x : ↥(Subgroup.center ↥Rs) => ((x : ↥Rs) : ↥L)) hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact absurd hv.symm hz1
        · exact absurd hv.symm hz21
        · exact absurd hv.symm hy1
        · exact absurd hv hz1
        · rfl
        · exact absurd hv hzz
        · exact absurd hv.symm hyz
        · exact absurd hv hz21
        · exact absurd hv.symm hzz
        · rfl
        · exact absurd hv.symm hyz2
        · exact absurd hv hy1
        · exact absurd hv hyz
        · exact absurd hv hyz2
        · rfl
      have := Nat.card_le_card_of_injective f hf
      simpa using this
    exact congrArg Subtype.val (comm_of_card_27 (R := ↥Rs) hRcard h4 ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x, hxR, hxy⟩ := hex
  refine ⟨x, y⁻¹ * x⁻¹ * y * x, ?_, ?_, by group⟩
  ·
    rw [← hkerc, MonoidHom.mem_ker]
    have hk3 : Nat.card (redHom L e).ker = 3 := by rw [hkerc, hZ3]
    have hcard9 : Nat.card ((R : Subgroup ↥L).map (redHom L e)) = 3 ^ 2 := by
      have := card_eq_three_mul_of_ker_le (redHom L e) hk3 (B := R)
        (by rw [hkerc]; exact hcenterR)
      rw [hRcard] at this
      norm_num at this ⊢
      omega
    have hab := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard9
    have hxm : redHom L e x ∈ (R : Subgroup ↥L).map (redHom L e) := ⟨x, hxR, rfl⟩
    have hym : redHom L e y ∈ (R : Subgroup ↥L).map (redHom L e) := ⟨y, hyR', rfl⟩
    have hcomm := congrArg Subtype.val (hab.is_comm.comm ⟨_, hxm⟩ ⟨_, hym⟩)
    simp only [Subgroup.coe_mul] at hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc (redHom L e y)⁻¹ * (redHom L e x)⁻¹ * redHom L e y * redHom L e x
        = (redHom L e y)⁻¹ * (redHom L e x)⁻¹ * (redHom L e y * redHom L e x) := by group
      _ = (redHom L e y)⁻¹ * (redHom L e x)⁻¹ * (redHom L e x * redHom L e y) := by rw [hcomm]
      _ = 1 := by group
  · intro h
    apply hxy
    calc x * y = x * y * (y⁻¹ * x⁻¹ * y * x) := by rw [h, mul_one]
      _ = y * x := by group

omit [Finite V] in
theorem actS_redHom {L E : Subgroup (MulAut V)}
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (e : CQ L ≃* ↥NativeSporadic.M22)
    (h : ↥(L ⊔ E)) (x : ↥L) (hx : (h : MulAut V) * x * (h : MulAut V)⁻¹ ∈ L) :
    actS hE e h (redHom L e x) = redHom L e ⟨(h : MulAut V) * x * (h : MulAut V)⁻¹, hx⟩ := by
  rw [actS_apply, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, redHom_apply, MulEquiv.symm_apply_apply]
  congr 1

theorem conj_mul_central {G : Type*} [Group G] {z a x : G} (hz : z ∈ Subgroup.center G) :
    (z * a) * x * (z * a)⁻¹ = a * x * a⁻¹ := by
  have h := Subgroup.mem_center_iff.1 hz (a * x * a⁻¹)
  calc (z * a) * x * (z * a)⁻¹ = z * (a * x * a⁻¹) * z⁻¹ := by group
    _ = (a * x * a⁻¹) * z * z⁻¹ := by rw [← h]
    _ = a * x * a⁻¹ := by group

theorem commutator_mul_central {G : Type*} [Group G] {z₁ z₂ a b : G}
    (h1 : z₁ ∈ Subgroup.center G) (h2 : z₂ ∈ Subgroup.center G) :
    (z₁ * a) * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  rw [conj_mul_central h1]
  have ha := Subgroup.mem_center_iff.1 h2 a
  have hc := Subgroup.mem_center_iff.1 h2 (a * b * a⁻¹ * b⁻¹)
  calc a * (z₂ * b) * a⁻¹ * (z₂ * b)⁻¹ = (a * z₂) * b * a⁻¹ * b⁻¹ * z₂⁻¹ := by group
    _ = z₂ * (a * b * a⁻¹ * b⁻¹) * z₂⁻¹ := by rw [ha]; group
    _ = (a * b * a⁻¹ * b⁻¹) * z₂ * z₂⁻¹ := by rw [← hc]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutator_inv_right {G : Type*} [Group G] {a b : G}
    (hc : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G) :
    a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by
  have h := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hc) b
  calc a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = b⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * b := by group
    _ = b⁻¹ * (b * (a * b * a⁻¹ * b⁻¹)⁻¹) := by rw [mul_assoc, ← h]
    _ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group

theorem exists_center_inverted
    (hW : ∀ w : V, w * w = 1) {L E : Subgroup (MulAut V)} (hperf : Group.IsPerfect ↥L)
    (hirr : IsIrrOn L) (hZ3 : Nat.card (Subgroup.center ↥L) = 3)
    (e : CQ L ≃* ↥NativeSporadic.M22) (hE : E ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hEel : IsElemAbelian2 E) {t : MulAut V} (htE : t ∈ E) (htL : t ∉ L) :
    ∃ c : ↥L, c ∈ Subgroup.center ↥L ∧ c ≠ 1 ∧ t * (c : MulAut V) * t⁻¹ = (c : MulAut V)⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLcard := card_hatL hZ3 e
  have hkerc : (redHom L e).ker = Subgroup.center ↥L := by
    ext g
    rw [MonoidHom.mem_ker, redHom_eq_one_iff]
  have hk3 : Nat.card (redHom L e).ker = 3 := by rw [hkerc, hZ3]
  set th : ↥(L ⊔ E) := ⟨t, Subgroup.mem_sup_right htE⟩ with hth
  set α := actS hE e th with hα
  have hαo : α ∉ inner ↥NativeSporadic.M22 := fun h =>
    htL (mem_of_actS_inner hW hperf hirr hE hEel e htE h)
  obtain ⟨g, hg, hαg⟩ := m22_outer_eq_conj α hαo
  set u : Equiv.Perm (Fin 22) := g * m22Delta with hu
  have htn : ∀ x ∈ L, t * x * t⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hE htE) x).1 hx
  have hconj : ∀ x : ↥L, ((redHom L e ⟨t * x * t⁻¹, htn x x.2⟩ : ↥NativeSporadic.M22) :
      Equiv.Perm (Fin 22)) = u * (redHom L e x : Equiv.Perm (Fin 22)) * u⁻¹ := by
    intro x
    rw [← actS_redHom hE e th x (htn x x.2), ← hα, hαg]
  have hδ' := inv_conj_mem NativeSporadic.M22 m22_delta_normalizes m22_delta_sq
  have hn : u⁻¹ * m22Sbar ∈ NativeSporadic.M22 := by
    have e1 : u⁻¹ * m22Sbar = (m22Delta⁻¹ * g⁻¹ * m22Delta) *
        evalCodes [m22gA, m22gB] m22SbarWord := by
      rw [hu, m22Sbar]
      group
    rw [e1]
    exact NativeSporadic.M22.mul_mem (hδ' _ (NativeSporadic.M22.inv_mem hg))
      (m22_evalCodes_mem _)
  obtain ⟨ℓ, hℓ⟩ := redHom_surjective L e ⟨_, hn⟩
  set s : MulAut V := t * (ℓ : MulAut V) with hsdef
  have hsn : ∀ x ∈ L, s * x * s⁻¹ ∈ L := fun x hx => by
    have : s * x * s⁻¹ = t * ((ℓ : MulAut V) * x * (ℓ : MulAut V)⁻¹) * t⁻¹ := by
      rw [hsdef]
      group
    rw [this]
    exact htn _ (L.mul_mem (L.mul_mem ℓ.2 hx) (L.inv_mem ℓ.2))
  have hsconj : ∀ x : ↥L, ((redHom L e ⟨s * x * s⁻¹, hsn x x.2⟩ : ↥NativeSporadic.M22) :
      Equiv.Perm (Fin 22)) = m22Sbar * (redHom L e x : Equiv.Perm (Fin 22)) * m22Sbar⁻¹ := by
    intro x
    have hlx : (ℓ : MulAut V) * x * (ℓ : MulAut V)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem ℓ.2 x.2) (L.inv_mem ℓ.2)
    have e1 : (⟨s * x * s⁻¹, hsn x x.2⟩ : ↥L) =
        ⟨t * ((ℓ * x * ℓ⁻¹ : ↥L) : MulAut V) * t⁻¹, htn _ (ℓ * x * ℓ⁻¹).2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsdef]
      group
    rw [e1, hconj, map_mul, map_mul, map_inv, hℓ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hs' : m22Sbar = u * (u⁻¹ * m22Sbar) := by group
    conv_rhs => rw [hs']
    group
  obtain ⟨a, ha⟩ := redHom_surjective L e m22A
  obtain ⟨b, hb⟩ := redHom_surjective L e m22B
  set c : ↥L := a * b * a⁻¹ * b⁻¹ with hcdef
  have hcC : c ∈ Subgroup.center ↥L := by
    rw [← redHom_eq_one_iff L e, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb,
      m22A_mul_B]
    group
  have hc1 : c ≠ 1 := by
    intro h1
    have hab : a * b = b * a := by
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [← hcdef, h1, one_mul]
    set R : Subgroup ↥L := m22Pbar.comap (redHom L e) with hRdef
    have hRcard : Nat.card R = 3 ^ 3 := by
      have h3 := card_eq_three_mul_of_ker_le (redHom L e) hk3 (B := R)
        (by intro x hx; rw [hRdef, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]; exact one_mem _)
      rw [hRdef, Subgroup.map_comap_eq_self_of_surjective (redHom_surjective L e),
        card_m22Pbar] at h3
      rw [h3]
      norm_num
    have hRle : R ≤ Subgroup.closure ({a, b} ∪ (Subgroup.center ↥L : Set ↥L)) := by
      intro x hx
      have hx' : redHom L e x ∈ m22Pbar := hx
      have hmap : m22Pbar = (Subgroup.closure {a, b}).map (redHom L e) := by
        rw [MonoidHom.map_closure, Set.image_pair, ha, hb]
        rfl
      rw [hmap] at hx'
      obtain ⟨w, hw, hwx⟩ := hx'
      have hk : w⁻¹ * x ∈ Subgroup.center ↥L := by
        rw [← redHom_eq_one_iff L e, map_mul, map_inv, hwx, inv_mul_cancel]
      have : x = w * (w⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.closure_mono Set.subset_union_left hw)
        (Subgroup.subset_closure (Set.mem_union_right _ hk))
    have hpair : ({a, b} ∪ (Subgroup.center ↥L : Set ↥L)).Pairwise Commute := by
      intro p hp q hq _
      rcases hp with hp | hp
      · rcases hq with hq | hq
        · rcases hp with rfl | hp <;> rcases hq with rfl | hq
          · exact Commute.refl _
          · rw [Set.mem_singleton_iff] at hq
            subst hq
            exact hab
          · rw [Set.mem_singleton_iff] at hp
            subst hp
            exact hab.symm
          · rw [Set.mem_singleton_iff] at hp hq
            subst hp hq
            exact Commute.refl _
        · exact Subgroup.mem_center_iff.1 hq p
      · exact (Subgroup.mem_center_iff.1 hp q).symm
    have hcomm := (Subgroup.isMulCommutative_closure hpair).is_comm.comm
    let RS : Sylow 3 ↥L := Sylow.ofCard R (by
      rw [hRcard, hLcard, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.add_apply, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero])
    obtain ⟨⟨z, hzC⟩, hz3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 3
      (by rw [hZ3])
    rw [Subgroup.orderOf_mk] at hz3
    have hzR : z ∈ RS := mem_sylow_three_of_central RS hzC hz3
    have hzc : z ∈ commutator ↥L := by
      rw [(Group.isPerfect_def).1 hperf]
      exact Subgroup.mem_top z
    have hz1 := central_mem_commutator_eq_one_of_abelian_sylow RS (fun p hp q hq => by
      have := hcomm ⟨p, hRle hp⟩ ⟨q, hRle hq⟩
      exact congrArg Subtype.val this) hzC hzR hzc
    rw [hz1, orderOf_one] at hz3
    norm_num at hz3
  have hsa : (⟨s * a * s⁻¹, hsn a a.2⟩ : ↥L) * a⁻¹ ∈ Subgroup.center ↥L := by
    rw [← redHom_eq_one_iff L e, map_mul, map_inv]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hsconj, ha]
    show m22Sbar * m22Abar * m22Sbar⁻¹ * m22Abar⁻¹ = 1
    rw [m22Sbar_conj_a, mul_inv_cancel]
  have hsb : (⟨s * b * s⁻¹, hsn b b.2⟩ : ↥L) * b ∈ Subgroup.center ↥L := by
    rw [← redHom_eq_one_iff L e, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, hsconj, hb]
    show m22Sbar * m22Bbar * m22Sbar⁻¹ * m22Bbar = 1
    rw [m22Sbar_conj_b, inv_mul_cancel]
  set z₁ := (⟨s * a * s⁻¹, hsn a a.2⟩ : ↥L) * a⁻¹ with hz₁
  set z₂ := (⟨s * b * s⁻¹, hsn b b.2⟩ : ↥L) * b with hz₂
  have hsa' : (⟨s * a * s⁻¹, hsn a a.2⟩ : ↥L) = z₁ * a := by rw [hz₁]; group
  have hsb' : (⟨s * b * s⁻¹, hsn b b.2⟩ : ↥L) = z₂ * b⁻¹ := by rw [hz₂]; group
  have hsc : (⟨s * c * s⁻¹, hsn c c.2⟩ : ↥L) = c⁻¹ := by
    have e1 : (⟨s * c * s⁻¹, hsn c c.2⟩ : ↥L) =
        (z₁ * a) * (z₂ * b⁻¹) * (z₁ * a)⁻¹ * (z₂ * b⁻¹)⁻¹ := by
      apply Subtype.ext
      have ha' := congrArg Subtype.val hsa'
      have hb' := congrArg Subtype.val hsb'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at ha' hb' ⊢
      rw [← ha', ← hb', hcdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1, commutator_mul_central hsa hsb, commutator_inv_right hcC]
  refine ⟨c, hcC, hc1, ?_⟩
  have h1 := congrArg Subtype.val hsc
  simp only [Subgroup.coe_inv] at h1
  have hlc : (ℓ : MulAut V) * c * (ℓ : MulAut V)⁻¹ = c := by
    have := Subgroup.mem_center_iff.1 hcC ℓ
    have h' := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h'
    rw [h', mul_inv_cancel_right]
  calc t * (c : MulAut V) * t⁻¹ = t * ((ℓ : MulAut V) * c * (ℓ : MulAut V)⁻¹) * t⁻¹ := by
        rw [hlc]
    _ = s * c * s⁻¹ := by rw [hsdef]; group
    _ = (c : MulAut V)⁻¹ := h1

theorem card_le_of_hatM22
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L)
    (hT : B45TypeHatM22 ↥L) (hq2 : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) :
    Nat.card V ≤ 2 ^ 24 := by
  obtain ⟨hq, hZ3, ⟨e⟩⟩ := hT
  have e' : CQ L ≃* ↥NativeSporadic.M22 := e
  have hW : ∀ v : V, v * v = 1 := fun v => by rw [← sq]; exact hV v
  have hirr : IsIrrOn L :=
    CFSG.QuasithinUnique.Bridge.Dichotomy.isIrrOn_of_isIrrSec hHyp.2.2.2
  have hperf : Group.IsPerfect ↥L := hq.1
  have hGN := B42L2.le_normalizer_of_b4Hyp hHyp
  obtain ⟨A, hA, -, hAr⟩ := kq_le_iff.mp hq2
  have hAV := (rAV_le_two_iff hV hA).mp hAr
  have hAidx := B45Exc.index_le_sq_of_offender2 A hAV
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := hA.1.trans hGN
  have hAel := hA.isElemAbelian2
  by_cases hAL : A ≤ L
  ·
    have hcardA : Nat.card A ≤ 2 ^ 4 := card_le_two_pow_of_le hW hirr hAL hAel e' m22_rank_le
    obtain ⟨⟨t, htA⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.ne_bot
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have htt : t * t = 1 := by rw [← sq]; exact hAel.2 t htA
    set tL : ↥L := ⟨t, hAL htA⟩
    have htL2 : tL * tL = 1 := Subtype.ext htt
    have htL1 : tL ≠ 1 := fun h => ht1' (congrArg Subtype.val h)
    obtain ⟨s, hss, hts3, htsc⟩ := exists_partner_lift hZ3 e' htL2 htL1
    obtain ⟨x, c, hcC, hc1, hxc⟩ := exists_conj_mul_center hZ3 hperf e' hts3 htsc
    have hcz : Commute ((tL * s : ↥L) : MulAut V) (c : MulAut V) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hcC (tL * s))
    have hxz : Commute (x : MulAut V) (c : MulAut V) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hcC x)
    have hc3 : (c : MulAut V) ^ 3 = 1 := by
      have := congrArg Subtype.val (pow_three_of_mem_center hZ3 hcC)
      rwa [SubgroupClass.coe_pow] at this
    have hbound := card_le_index_cube hW (x := (x : MulAut V)) (t := t) (s := (s : MulAut V))
      hc3 (fixV_center_eq_bot hirr hcC hc1) htt (congrArg Subtype.val hss)
      (by have := congrArg Subtype.val hts3; rwa [SubgroupClass.coe_pow] at this)
      hcz hxz (by have := congrArg Subtype.val hxc; simpa using this)
    have h1 : (fixV (Subgroup.zpowers t)).index ≤ (fixV A).index :=
      Subgroup.index_antitone (fixV_anti ((Subgroup.zpowers_le).2 htA))
    calc Nat.card V ≤ (fixV (Subgroup.zpowers t)).index ^ 3 := hbound
      _ ≤ (Nat.card A ^ 2) ^ 3 := Nat.pow_le_pow_left (h1.trans hAidx) 3
      _ ≤ ((2 ^ 4) ^ 2) ^ 3 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hcardA 2) 3
      _ = 2 ^ 24 := by norm_num
  ·
    obtain ⟨t, htA, htL⟩ : ∃ t ∈ A, t ∉ L := by
      by_contra h
      push Not at h
      exact hAL h
    have hAel' : IsElemAbelian2 (A ⊓ L) :=
      ⟨fun a ha b hb => hAel.1 a ha.1 b hb.1, fun a ha => hAel.2 a ha.1⟩
    have hcard0 : Nat.card ↥(A ⊓ L) ≤ 2 ^ 4 :=
      card_le_two_pow_of_le hW hirr inf_le_right hAel' e' m22_rank_le
    have hcard2 := card_le_two_mul_inf hW hperf hirr hAN hAel e' m22_center_eq_bot'
      m22_mulAut_card
    have hcardA : Nat.card A ≤ 2 ^ 5 := by
      calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := hcard2
        _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul_left _ hcard0
        _ = 2 ^ 5 := by norm_num
    obtain ⟨c, hcC, hc1, htc⟩ := exists_center_inverted hW hperf hirr hZ3 e' hAN hAel htA htL
    have hc3 : (c : MulAut V) ^ 3 = 1 := by
      have := congrArg Subtype.val (pow_three_of_mem_center hZ3 hcC)
      rwa [SubgroupClass.coe_pow] at this
    have hbound := card_le_index_sq_of_inverts hc3 (fixV_center_eq_bot hirr hcC hc1) htc
    have h1 : (fixV (Subgroup.zpowers t)).index ≤ (fixV A).index :=
      Subgroup.index_antitone (fixV_anti ((Subgroup.zpowers_le).2 htA))
    calc Nat.card V ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := hbound
      _ ≤ (Nat.card A ^ 2) ^ 2 := Nat.pow_le_pow_left (h1.trans hAidx) 2
      _ ≤ ((2 ^ 5) ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hcardA 2) 2
      _ ≤ 2 ^ 24 := by norm_num

end CFSG.Quasithin.HatM22
