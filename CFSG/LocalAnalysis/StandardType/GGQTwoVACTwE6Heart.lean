module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSymp
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6Realization
public import CFSG.LocalAnalysis.StandardType.GGQTwoE6HeartWeyl
public import CFSG.LocalAnalysis.StandardType.GGTPNPCompQuasi
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACExc
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartReduction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem isPGroup_sup_zpowers {G : Type} [Group G] {x c : G} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hcx : Commute c x) :
    IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) := by
  have hxP : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (p := 3) (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
    norm_num
  have hcP : IsPGroup 3 (Subgroup.zpowers c) := by
    by_cases hc1 : c = 1
    · rw [hc1, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_card (p := 3) (n := 0) (by simp)
    · refine IsPGroup.of_card (p := 3) (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
      norm_num
  have hcomm_xc : ∀ a ∈ Subgroup.zpowers x, ∀ d ∈ Subgroup.zpowers c, a * d = d * a := by
    intro a ha d hd
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ((hcx.symm.zpow_left m).zpow_right n).eq
  have hcentc : Subgroup.zpowers x ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm_xc a ha y hy).symm
  exact IsPGroup.to_sup_of_normal_right' hxP hcP
    (hcentc.trans (Subgroup.centralizer_le_normalizer _))

theorem mem_zpowers_of_centralizer_orderThree {G : Type} [Group G] [Finite G] {x c : G}
    {L : Subgroup G}
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hc3 : c ^ 3 = 1) (hcx : Commute c x)
    (hxC : x ∈ Subgroup.centralizer (L : Set G))
    (hc : c ∈ Subgroup.centralizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
      IsCyclic S) :
    c ∈ Subgroup.zpowers x := by
  have hsupP : IsPGroup 3 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) :=
    isPGroup_sup_zpowers hx1 hx3 hc3 hcx
  have hxEA : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers hx3
  have hcEA : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers c) :=
    CFSG.Open.isElemAbelian_zpowers hc3
  have hcomm_xc : ∀ a ∈ Subgroup.zpowers x, ∀ d ∈ Subgroup.zpowers c, a * d = d * a := by
    intro a ha d hd
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ((hcx.symm.zpow_left m).zpow_right n).eq
  have hsupEA := CFSG.Open.IsElemAbelian.sup_of_commute hxEA hcEA hcomm_xc
  have hsup_mem : Subgroup.zpowers x ⊔ Subgroup.zpowers c ≤
      Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxC) (Subgroup.zpowers_le.mpr hc)
  have hcyc_sup : IsCyclic ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) :=
    hcyc _ hsup_mem hsupP
  have hxle : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers c := le_sup_left
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hsup_card : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers c) ≤ 3 :=
    TableB.card_le_of_isCyclic (by norm_num) hcyc_sup (fun y hy => hsupEA.2 y hy)
  have hsup_eq : Subgroup.zpowers x = Subgroup.zpowers x ⊔ Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers x) (K := _) hxle
      (by rw [hcardx]; exact hsup_card)
  have hc_mem : c ∈ Subgroup.zpowers x := by
    rw [hsup_eq]
    exact (le_sup_right : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c)
  exact hc_mem

theorem apply_eq_of_commute_conj {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥)
    {s : MulAut H} {t : H} (h : s * MulAut.conj t = MulAut.conj t * s) : s t = t := by
  have hconj : MulAut.conj (s t) = MulAut.conj t := by
    have h1 : s * MulAut.conj t * s⁻¹ = MulAut.conj (s t) := by
      ext y
      change s (t * (MulEquiv.symm s) y * t⁻¹) = s t * y * (s t)⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [← h1, h, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : (s t)⁻¹ * t ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : MulAut.conj ((s t)⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hconj, inv_mul_cancel]
    have h2' := congrArg (fun f : MulAut H => f y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2'
    have h2 : ((s t)⁻¹ * t) * y * ((s t)⁻¹ * t)⁻¹ = y := h2'
    have h3 : ((s t)⁻¹ * t) * y = y * ((s t)⁻¹ * t) := by
      calc ((s t)⁻¹ * t) * y =
          (((s t)⁻¹ * t) * y * ((s t)⁻¹ * t)⁻¹) * ((s t)⁻¹ * t) := by group
        _ = y * ((s t)⁻¹ * t) := by rw [h2]
    exact h3.symm
  have h1 : (s t)⁻¹ * t = 1 := by simpa [hZ] using hmem
  calc s t = (s t) * ((s t)⁻¹ * t) := by rw [h1, mul_one]
    _ = t := by group

theorem mem_zpowers_of_central_center {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {w : G}
    (hwL : w ∈ L) (hwC : w ∈ Subgroup.centralizer (L : Set G)) (hw3 : w ^ 3 = 1) :
    w ∈ Subgroup.zpowers x := by
  have hSstar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hxB, hx1, hComp, hcyc⟩ := hSstar
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hxB
  have hx3 : x ^ 3 = 1 := by
    have := (hS.1.1.tableB_facts).2.1.2 x hxBs
    simpa using this
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_le_centralizer hComp.1
  exact mem_zpowers_of_centralizer_orderThree hx1 hx3 hw3 (hxC w hwL) hxC hwC hcyc

theorem not_dvd_center_of_not_mem {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∉ L) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by
  intro hdvd
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥L) 3 hdvd
  let w : G := (((z : Subgroup.center ↥L) : ↥L) : G)
  have hwL : w ∈ L := ((z : Subgroup.center ↥L) : ↥L).2
  have hwod : orderOf w = 3 := by
    calc orderOf w = orderOf ((z : Subgroup.center ↥L) : ↥L) := Subgroup.orderOf_coe _
      _ = orderOf (z : Subgroup.center ↥L) := Subgroup.orderOf_coe _
      _ = 3 := hzord
  have hw3 : w ^ 3 = 1 := by
    rw [← hwod]
    exact pow_orderOf_eq_one w
  have hwC : w ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcomm := Subgroup.mem_center_iff.mp z.2 (⟨y, hy⟩ : ↥L)
    have hcoe := congrArg (fun u : ↥L => (u : G)) hcomm
    simpa [w, mul_comm] using hcoe
  have hw_mem : w ∈ Subgroup.zpowers x := mem_zpowers_of_central_center hS hwL hwC hw3
  have hSstar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hxB, hx1, hComp, _⟩ := hSstar
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hxB
  have hx3 : x ^ 3 = 1 := by
    have := (hS.1.1.tableB_facts).2.1.2 x hxBs
    simpa using this
  have hw1 : w ≠ 1 := by
    intro h1
    have : orderOf w = 1 := by rw [h1, orderOf_one]
    omega
  have hcardw : Nat.card (Subgroup.zpowers w) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hw3 hw1
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have heq : Subgroup.zpowers w = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw_mem)
      (by rw [hcardx, hcardw])
  have hxw : x ∈ Subgroup.zpowers w := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact hxL (Subgroup.zpowers_le.mpr hwL hxw)

theorem exists_order_three_lift
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    (hcp : ¬ 3 ∣ Nat.card (Subgroup.center ↥L))
    (t : twistedE6RootGroup K σ) (ht3 : t ^ 3 = 1) :
    ∃ ℓ : L, ℓ ^ 3 = 1 ∧
      θ (QuotientGroup.mk ℓ : L ⧸ Subgroup.center L) =
        (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)).symm t := by
  classical
  let eR := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  let ℓbar : L ⧸ Subgroup.center L := θ.symm (eR.symm t)
  have hℓbar3 : ℓbar ^ 3 = 1 := by
    rw [show ℓbar = θ.symm (eR.symm t) from rfl, ← map_pow, ← map_pow, ht3, map_one, map_one]
  obtain ⟨ℓ, hℓ, hℓ3⟩ := exists_lift_pow_eq_one (p := 3) Nat.prime_three
    (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
    (le_of_eq (QuotientGroup.ker_mk' (Subgroup.center ↥L))) hcp (g := ℓbar) hℓbar3
  refine ⟨ℓ, hℓ3, ?_⟩
  change θ (QuotientGroup.mk ℓ) = eR.symm t
  rw [show (QuotientGroup.mk ℓ : L ⧸ Subgroup.center L) = ℓbar from hℓ]
  exact θ.apply_symm_apply _

theorem beta_fixes_of_commute
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    {Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hSdef : S = (ggBeta L θ hN).range.map
      (MulAut.congr (centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom)
    (hYEA : IsElemAbelian 3 Y) (hSlang : S ≤ Y)
    {t : twistedE6RootGroup K σ} {h : MulAut ↥(twistedE6RootGroup K σ)}
    (hhY : h ∈ Y) (ht : h = MulAut.conj t)
    {b : G} (hb : b ∈ Bs) :
    ggBeta L θ hN (⟨b, hb⟩ : Bs)
      ((centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)).symm t) =
    (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)).symm t := by
  classical
  let eR := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  let s : MulAut ↥(twistedE6RootGroup K σ) :=
    MulAut.congr eR (ggBeta L θ hN (⟨b, hb⟩ : Bs))
  have hsS : s ∈ S := by
    rw [hSdef]
    exact Subgroup.mem_map_of_mem _ ⟨⟨b, hb⟩, rfl⟩
  have hsY : s ∈ Y := hSlang hsS
  have hcomm : s * h = h * s := TableB.IsElemAbelian.comm hYEA hsY hhY
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hst : s t = t := by
    apply apply_eq_of_commute_conj hZ
    simpa [ht] using hcomm
  have h1 : eR (ggBeta L θ hN (⟨b, hb⟩ : Bs) (eR.symm t)) = s t := by
    dsimp [s]
    change eR (ggBeta L θ hN (⟨b, hb⟩ : Bs) (eR.symm t)) =
      eR (ggBeta L θ hN (⟨b, hb⟩ : Bs) (eR.symm t))
    rfl
  rw [← eR.injective.eq_iff]
  rw [h1, hst, eR.apply_symm_apply]

theorem center_eq_one_of_pow_three
    {G : Type} [Group G] {L : Subgroup G}
    (hcp : ¬ 3 ∣ Nat.card (Subgroup.center ↥L))
    {z' : ↥L} (hz'Z : z' ∈ Subgroup.center ↥L) (hz'3 : (z' : ↥L) ^ 3 = 1) : z' = 1 := by
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact hcp
  have hdvd : orderOf z' ∣ 1 := by
    have hd3 : orderOf z' ∣ 3 := orderOf_dvd_of_pow_eq_one hz'3
    have hdZ : orderOf z' ∣ Nat.card (Subgroup.center ↥L) := by
      rw [Subgroup.orderOf_coe (⟨z', hz'Z⟩ : Subgroup.center ↥L)]
      exact orderOf_dvd_natCard _
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hd3 hdZ
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem heart_lift_centralizes
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    {Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hSdef : S = (ggBeta L θ hN).range.map
      (MulAut.congr (centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom)
    (hYEA : IsElemAbelian 3 Y) (hSlang : S ≤ Y)
    (hcp : ¬ 3 ∣ Nat.card (Subgroup.center ↥L))
    {t : twistedE6RootGroup K σ} {h : MulAut ↥(twistedE6RootGroup K σ)}
    (hhY : h ∈ Y) (ht : h = MulAut.conj t)
    {ℓ : L} (hℓ : θ (QuotientGroup.mk ℓ : L ⧸ Subgroup.center L) =
      (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)).symm t)
    (hℓ3 : ℓ ^ 3 = 1) :
    ∀ b ∈ Bs, (b : G) * (ℓ : G) = (ℓ : G) * (b : G) := by
  classical
  let eR := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  intro b hb
  have hβfix := beta_fixes_of_commute (K := K) (σ := σ) hSdef hYEA hSlang hhY ht hb
  have hq : QuotientGroup.mk (L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ) =
      (QuotientGroup.mk ℓ : L ⧸ Subgroup.center L) := by
    apply θ.injective
    rw [← ggLAut_apply (g := (⟨b, hN hb⟩ : Subgroup.normalizer (L : Set G))) (l := ℓ)]
    change ggBeta L θ hN (⟨b, hb⟩ : Bs) (θ (QuotientGroup.mk ℓ)) = θ (QuotientGroup.mk ℓ)
    rw [hℓ]
    exact hβfix
  have hz : (L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ)⁻¹ * ℓ ∈ Subgroup.center ↥L :=
    QuotientGroup.eq.mp hq
  let z : ↥L := (L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ)⁻¹ * ℓ
  have hzZ : (z : ↥L) ∈ Subgroup.center ↥L := hz
  let z' : ↥L := z⁻¹
  have hz'Z : z' ∈ Subgroup.center ↥L := Subgroup.inv_mem _ hzZ
  have hℓ' : L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ = ℓ * z' := by
    dsimp [z, z']
    group
  have hz'3 : (z' : ↥L) ^ 3 = 1 := by
    have hcz : Commute (ℓ : ↥L) z' := (Subgroup.mem_center_iff.mp hz'Z) ℓ
    have hconj3 : (L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ) ^ 3 = 1 := by
      rw [← map_pow, hℓ3, map_one]
    have h1 : ((ℓ : ↥L) * z') ^ 3 = 1 := hℓ' ▸ hconj3
    rwa [hcz.mul_pow, hℓ3, one_mul] at h1
  have hz'1 : z' = 1 := center_eq_one_of_pow_three (L := L) hcp hz'Z hz'3
  have hconj : (b : G) * (ℓ : G) * (b : G)⁻¹ = (ℓ : G) := by
    have h1 : ((L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ : ↥L) : G) = (b : G) * (ℓ : G) * (b : G)⁻¹ :=
      normalizerMonoidHom_coe (L := L)
        (⟨b, hN hb⟩ : Subgroup.normalizer (L : Set G)) ℓ
    rw [← h1, hℓ', hz'1, mul_one]
  have := congrArg (fun x : G => x * b) hconj
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using this

theorem eq_one_of_conj_eq_one {H : Type*} [Group H] (hZ : Subgroup.center H = ⊥) {x : H}
    (h : MulAut.conj x = 1) : x = 1 := by
  have hmem : x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 : x * y * x⁻¹ = y := by
      simpa [MulAut.conj_apply] using congrArg (fun f : MulAut H => f y) h
    calc y * x = (x * y * x⁻¹) * x := by rw [h2]
      _ = x * y := by group
  simpa [hZ] using hmem

theorem heart_lift_mem_bstar {G : Type} [Group G] {Bs L : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {ℓ : L} (hcent : ∀ b ∈ Bs, (b : G) * (ℓ : G) = (ℓ : G) * (b : G))
    (hℓ3 : ℓ ^ 3 = 1) : (ℓ : G) ∈ Bs := by
  apply hSC (ℓ : G)
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcent b hb
  · simpa using congrArg (fun z : ↥L => (z : G)) hℓ3

theorem beta_heart_lift_eq
    {G : Type} [Group G] {Bs : Subgroup G} {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)} {ℓ : L} (hℓB : (ℓ : G) ∈ Bs)
    {t : twistedE6RootGroup K σ} {h : MulAut ↥(twistedE6RootGroup K σ)}
    (hℓ : θ (QuotientGroup.mk ℓ : L ⧸ Subgroup.center L) =
      (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)).symm t)
    (ht : h = MulAut.conj t) :
    MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ))
      (ggBeta L θ hN (⟨(ℓ : G), hℓB⟩ : Bs)) = h := by
  let eR := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  have hβ : ggBeta L θ hN (⟨(ℓ : G), hℓB⟩ : Bs) =
      MulAut.conj (θ (QuotientGroup.mk ℓ)) := by
    rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
    have hg : L.normalizerMonoidHom
        (⟨(ℓ : G), hN hℓB⟩ : Subgroup.normalizer (L : Set G)) = MulAut.conj ℓ := by
      ext y
      rfl
    rw [hg]
    exact tpq_ggInducedAut_conj θ ℓ
  rw [hβ, hℓ, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
    eR.apply_symm_apply, ← ht]

theorem exists_heart_lift_mem_bstar
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {S Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hSdef : S = (ggBeta L θ hN).range.map
      (MulAut.congr (centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom)
    (hYEA : IsElemAbelian 3 Y) (hSlang : S ≤ Y)
    (hcp : ¬ 3 ∣ Nat.card (Subgroup.center ↥L))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {h : MulAut ↥(twistedE6RootGroup K σ)}
    (hh : h ∈ Y ⊓ (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
      MulAut ↥(twistedE6RootGroup K σ)).range) :
    ∃ ℓ : L, ∃ hℓB : (ℓ : G) ∈ Bs, ℓ ^ 3 = 1 ∧
      MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ))
        (ggBeta L θ hN (⟨(ℓ : G), hℓB⟩ : Bs)) = h := by
  obtain ⟨hhY, t, rfl⟩ := hh
  have ht3 : t ^ 3 = 1 := by
    apply eq_one_of_conj_eq_one (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    rw [map_pow]
    exact hYEA.2 _ hhY
  obtain ⟨ℓ, hℓ3, hℓ⟩ := exists_order_three_lift (θ := θ) hcp t ht3
  have hcent := heart_lift_centralizes hSdef hYEA hSlang hcp hhY rfl hℓ hℓ3
  have hℓB : (ℓ : G) ∈ Bs := heart_lift_mem_bstar hSC hcent hℓ3
  exact ⟨ℓ, hℓB, hℓ3, beta_heart_lift_eq hℓB hℓ rfl⟩

theorem inf_inner_le_beta_image
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {L : Subgroup G}
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    {S Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))}
    (hSdef : S = (ggBeta L θ hN).range.map
      (MulAut.congr (centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom)
    (hYEA : IsElemAbelian 3 Y) (hSlang : S ≤ Y)
    (hcp : ¬ 3 ∣ Nat.card (Subgroup.center ↥L))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    Y ⊓ (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
      MulAut ↥(twistedE6RootGroup K σ)).range ≤ S := by
  intro h hh
  obtain ⟨ℓ, hℓB, -, hℓ⟩ := exists_heart_lift_mem_bstar hSdef hYEA hSlang hcp hSC hh
  rw [hSdef]
  exact Subgroup.mem_map.mpr ⟨_, ⟨⟨(ℓ : G), hℓB⟩, rfl⟩, hℓ⟩

theorem mem_sup_zpowers_of_ggBeta_eq {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hperf : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {b ℓ : G} (hb : b ∈ Bs) (hℓB : ℓ ∈ Bs)
    (hℓL : ℓ ∈ L) (heq : ggBeta L θ hN ⟨b, hb⟩ = ggBeta L θ hN ⟨ℓ, hℓB⟩) :
    b ∈ L ⊔ Subgroup.zpowers x := by
  have hc : b * ℓ⁻¹ ∈ Bs := mul_mem hb (inv_mem hℓB)
  have h1 : ggBeta L θ hN ⟨b * ℓ⁻¹, hc⟩ = 1 := by
    have : (⟨b * ℓ⁻¹, hc⟩ : Bs) = ⟨b, hb⟩ * (⟨ℓ, hℓB⟩ : Bs)⁻¹ := rfl
    rw [this, map_mul, map_inv, heq, mul_inv_cancel]
  have hcent : b * ℓ⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_ggLAut_eq_one L θ hperf (g := ⟨b * ℓ⁻¹, hN hc⟩) h1
  have hx : b * ℓ⁻¹ ∈ Subgroup.zpowers x := by
    rw [← GGConfig.bstar_inf_centralizer_L hcfg]
    exact ⟨hc, hcent⟩
  have hb' : b = (b * ℓ⁻¹) * ℓ := by group
  rw [hb', sup_comm]
  exact Subgroup.mul_mem_sup hx hℓL

theorem ggQ2TwE6Heart_bstar_le_sup_zpowers
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .twE6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 5)
    (hxL : x ∉ L) :
    Bs ≤ L ⊔ Subgroup.zpowers x := by
  obtain ⟨K, _, _, σ, hK1, hσ1, θ, hN, S, Fr, hFr, g, -, -, hSdef, -, hScard, hg, hgn,
    hSlang, -⟩ := QTwoE6.actual_beta_langCube_of_marking hS rfl hq2 htag hmark hidx le_rfl
  let I : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) :=
    (MulAut.conj : ↥(twistedE6RootGroup K σ) →* MulAut ↥(twistedE6RootGroup K σ)).range
  let Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) :=
    TwE6DD2.langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g
  have hYEA : IsElemAbelian 3 Y :=
    TwE6DD2.isElemAbelian_langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g
  have hcp := not_dvd_center_of_not_mem hS hxL
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hS.1.1.2.1.2.2.2
  have hle : Y ⊓ I ≤ S := inf_inner_le_beta_image hSdef hYEA hSlang hcp hSC
  have hYI : Nat.card ↥(Y ⊓ I) = 3 ^ 5 :=
    QTwoE6.card_langCube_inf_inner hK1 σ hσ1 Fr hFr hg hgn
  have hSeq : Y ⊓ I = S := Subgroup.eq_of_le_of_card_ge hle (by rw [hScard, hYI])
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hperf : commutator L = ⊤ := hSS.2.2.2.1.2.2.1
  intro b hb
  have hbS : MulAut.congr (centerQuotEquivOfBot
      (exceptional_fixed_center_trivial TwistTag.E6 K σ)) (ggBeta L θ hN ⟨b, hb⟩) ∈ Y ⊓ I := by
    rw [hSeq, hSdef]
    exact Subgroup.mem_map.mpr ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
  obtain ⟨ℓ, hℓB, -, hℓ⟩ := exists_heart_lift_mem_bstar hSdef hYEA hSlang hcp hSC hbS
  exact mem_sup_zpowers_of_ggBeta_eq hS.1.1 hperf θ hN hb hℓB ℓ.2
    ((MulAut.congr _).injective hℓ).symm

theorem ggQTwoAutomizer_four_of_twE6_of_not_mem
    (hCav : GGQ2CavOfTBFull) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hL : GGInnerDiagOnLabel (fun _ lab => GGLabQTwo p lab ∧ lab.tag = .twE6) p Bs L)
    (hxL : x ∉ L) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  subst hp
  have hLkeep := hL
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, _, I, F, -, -, -, ⟨⟨hq, htag⟩, hN, -⟩⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := ggQ2Exc_label_n_eq_one hlab hq
  have hmarkLab : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab) :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ', _⟩ => ⟨hs, hna, θ', rfl⟩) hraw⟩
  have hsplit : LargeEvenSplit 3 lab := Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, htag],
    by simp [htag], by rw [hn1]; norm_num⟩)
  have hmarkTB : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L :=
    ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F h => by
        obtain ⟨hs, hna, θ, hθ⟩ := h
        exact ⟨hs, hna, θ, ⟨⟨htag, rfl, by rw [hn1]; norm_num⟩, hsplit,
          hθ.2.1, hθ.2.2⟩⟩) hraw⟩
  rcases ggQ2TwE6_index hS rfl (hN := hN) (ggQ2TwE6_lower hS rfl hmarkTB (hN := hN))
    (ggQ2TwE6_upper hS rfl hLkeep (hN := hN)) with h6 | h5
  · exact ggQTwoAutomizer_four_of_twE6Full hCav hS rfl hmarkLab hq htag
      (by simpa [GGQ2LieRank, htag] using h6)
  · have hmark := QTwoCav.innerDiagOnLabel_of_marking (p := 3) hS.1.2.2.1.1 hmarkLab
    have hsup := ggQ2TwE6Heart_bstar_le_sup_zpowers hS hq htag hmark h5 hxL
    have hTB : GGQ2TBHeart 3 Bs L :=
      ⟨lab, hq, hmarkLab, Or.inr htag, by simpa [GGQ2LieRank, htag] using h5⟩
    by_cases hJ : CFSG.AGLEmbedding.IsAltTwoP 3 J
    · rw [QTwoB2Cav.card_automizer_original_of_setting hS rfl hN hJ]
    · have h4 := ggQ2_cavOfTBHeartInner_holds hS rfl hTB hsup hJ hN
      rwa [QTwoCav.card_automizer_inner_image_eq_of_setting hS Nat.prime_three
        (by norm_num) hN] at h4

end CFSG.StandardType

end
