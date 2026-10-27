module

public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType.K1Lift

open CFSG.Assembly

@[expose] def K1b {Jb : Type*} [Group Jb] (rb : Jb) (Vb : Subgroup Jb) : Prop :=
  ∀ Y : Subgroup (MulAut Jb), IsPGroup 2 Y → (∀ φ ∈ Y, φ rb = rb) →
    (∀ c : Jb, c * rb = rb * c → MulAut.conj c ∈ Subgroup.normalizer (Y : Set (MulAut Jb))) →
    ∀ v ∈ Vb, ∀ φ ∈ Y, φ v * v⁻¹ ∈ Subgroup.zpowers rb

private lemma conj_sq {G : Type*} [Group G] (j r : G) :
    (j * r * j⁻¹) ^ 2 = j * r ^ 2 * j⁻¹ := by
  conv_lhs => rw [← MulAut.conj_apply j r]
  rw [← map_pow, MulAut.conj_apply]

private lemma center_eq_one_of_sq_eq_one {X : Type*} [Group X] {J : Subgroup X}
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) {x : ↥J}
    (hx : x ∈ Subgroup.center ↥J) (hx2 : x ^ 2 = 1) : x = 1 := by
  have hdvd2 : orderOf x ∣ 2 := (orderOf_dvd_iff_pow_eq_one).2 hx2
  have hdvdZ : orderOf x ∣ Nat.card (Subgroup.center ↥J) :=
    Subgroup.orderOf_dvd_natCard _ hx
  have hcop : Nat.Coprime 2 (Nat.card (Subgroup.center ↥J)) :=
    hZ.coprime_two_right.symm
  have hdvd1 : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hdvd2 hdvdZ
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

private lemma center_eq_one_of_pow_four_eq_one {X : Type*} [Group X] {J : Subgroup X}
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) {x : ↥J}
    (hx : x ∈ Subgroup.center ↥J) (hx4 : x ^ 4 = 1) : x = 1 := by
  have h2 : (x ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hx4
  have hx2 : x ^ 2 = 1 := center_eq_one_of_sq_eq_one hZ (Subgroup.pow_mem _ hx 2) h2
  exact center_eq_one_of_sq_eq_one hZ hx hx2

private lemma map_isElemAbelian {G X : Type*} [Group G] [Group X] {p : ℕ}
    (H : Subgroup G) (f : G →* X) (hH : IsElemAbelian p H) :
    IsElemAbelian p (H.map f) := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨ha, hha, hae⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨hb, hhb, hbe⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : X) * b = (b : X) * a
    rw [← hae, ← hbe, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val
      (hH.1.is_comm.comm (⟨ha, hha⟩ : ↥H) (⟨hb, hhb⟩ : ↥H)))
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hH.2 g hg, map_one]

private noncomputable def normalizerAlpha {X : Type*} [Group X] (J : Subgroup X) :
    Subgroup.normalizer (J : Set X) →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
  MonoidHom.mk' (fun y => QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J)
      (Subgroup.normalizerMonoidHom J y)
      (Subgroup.map_center_eq (Subgroup.normalizerMonoidHom J y)))
    (by
      intro y y'
      ext q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
      simp only [QuotientGroup.congr_mk, MulAut.mul_apply, MonoidHom.map_mul])

private lemma normalizerAlpha_mk {X : Type*} [Group X] (J : Subgroup X)
    (y : Subgroup.normalizer (J : Set X)) (a : ↥J) :
    normalizerAlpha J y (QuotientGroup.mk a)
      = QuotientGroup.mk ((Subgroup.normalizerMonoidHom J y) a) := by
  change (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J)
      (Subgroup.normalizerMonoidHom J y)
      (Subgroup.map_center_eq (Subgroup.normalizerMonoidHom J y))) (QuotientGroup.mk a)
    = QuotientGroup.mk ((Subgroup.normalizerMonoidHom J y) a)
  rw [QuotientGroup.congr_mk]

private lemma normalizerAlpha_mk' {X : Type*} [Group X] (J : Subgroup X)
    (y : Subgroup.normalizer (J : Set X)) (a : ↥J) :
    normalizerAlpha J y ((QuotientGroup.mk' (Subgroup.center ↥J)) a)
      = (QuotientGroup.mk' (Subgroup.center ↥J))
          ((Subgroup.normalizerMonoidHom J y) a) := by
  change normalizerAlpha J y (QuotientGroup.mk a)
      = QuotientGroup.mk ((Subgroup.normalizerMonoidHom J y) a)
  exact normalizerAlpha_mk J y a

private lemma normalizerAlpha_conj {X : Type*} [Group X] (J : Subgroup X) (c : ↥J) :
    normalizerAlpha J ⟨(c : X), Subgroup.le_normalizer c.2⟩
      = MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) c) := by
  ext q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  rw [normalizerAlpha_mk]
  change (QuotientGroup.mk' (Subgroup.center ↥J))
        ((Subgroup.normalizerMonoidHom J ⟨(c : X), Subgroup.le_normalizer c.2⟩) a)
      = MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) c)
          ((QuotientGroup.mk' (Subgroup.center ↥J)) a)
  rw [MulAut.conj_apply]
  rw [← map_mul, ← map_inv, ← map_mul]
  apply congrArg (QuotientGroup.mk' (Subgroup.center ↥J))
  apply Subtype.ext
  simpa using Subgroup.normalizerMonoidHom_apply_apply_coe J
    ⟨(c : X), Subgroup.le_normalizer c.2⟩ a

theorem lemmaK {X : Type*} [Group X] [Finite X] {J : Subgroup X}
    (hJ : IsQuasisimple ↥J) (hZ : Odd (Nat.card (Subgroup.center ↥J)))
    {Vb : Subgroup (↥J ⧸ Subgroup.center ↥J)} {rb : ↥J ⧸ Subgroup.center ↥J}
    (hrb : rb ∈ Vb) (hrb1 : rb ≠ 1) (hVb : IsElemAbelian 2 Vb) (hVb4 : Nat.card Vb = 4)
    (hconj : ∀ v ∈ Vb, v ≠ 1 → ∃ j : ↥J ⧸ Subgroup.center ↥J, v = j * rb * j⁻¹)
    (hK1 : K1b rb Vb) :
    ∃ (V : Subgroup X) (r : X), r ∈ V ∧ V ≤ J ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 ∧
      r ∉ Subgroup.centralizer (J : Set X) ∧ (∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * r * j⁻¹) ∧
      (∃ r' : ↥J, (r' : X) = r ∧ QuotientGroup.mk' (Subgroup.center ↥J) r' = rb) ∧
      (V.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) = Vb ∧
      ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (J : Set X) →
        Y ≤ Subgroup.centralizer {r} →
        (∀ c ∈ J, c * r = r * c → c ∈ Subgroup.normalizer (Y : Set X)) →
        ∀ v ∈ V, ∀ y ∈ Y, ∃ k : ℤ, ∃ z ∈ Subgroup.centralizer (J : Set X),
          v * y * v⁻¹ * y⁻¹ = r ^ k * z := by
  classical
  let Z : Subgroup ↥J := Subgroup.center ↥J
  let Vt : Subgroup ↥J := Vb.comap (QuotientGroup.mk' Z)
  have hsurj : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hmap : Subgroup.map (QuotientGroup.mk' Z) Vt = Vb :=
    Subgroup.map_comap_eq_self_of_surjective hsurj Vb
  have h4dvd : 4 ∣ Nat.card Vt := by
    have h : Nat.card (Subgroup.map (QuotientGroup.mk' Z) Vt) ∣ Nat.card Vt :=
      Subgroup.card_map_dvd Vt (QuotientGroup.mk' Z)
    rwa [hmap, hVb4] at h
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Vt) 2 (n := 2) h4dvd
  let V₀ : Subgroup ↥J := K.map Vt.subtype
  have hV₀card : Nat.card V₀ = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Vt)]
    exact hKcard
  have hV₀le : V₀ ≤ Vt := Subgroup.map_subtype_le K
  have hV0_inj : ∀ x ∈ V₀, (QuotientGroup.mk' Z) x = 1 → x = 1 := by
    intro x hx hx1
    have hxZ : x ∈ Z := by
      have hxmk : (QuotientGroup.mk x : ↥J ⧸ Z) = 1 := by
        simpa only [QuotientGroup.mk'_apply] using hx1
      exact (QuotientGroup.eq_one_iff (N := Z) x).mp hxmk
    have hdvd : orderOf x ∣ 4 := by
      rw [← hV₀card]
      exact Subgroup.orderOf_dvd_natCard V₀ hx
    exact center_eq_one_of_pow_four_eq_one hZ hxZ ((orderOf_dvd_iff_pow_eq_one).mp hdvd)
  have hV0_inj' : ∀ x ∈ V₀, ∀ y ∈ V₀,
      (QuotientGroup.mk' Z) x = (QuotientGroup.mk' Z) y → x = y := by
    intro x hx y hy hxy
    have hmem : x * y⁻¹ ∈ V₀ := V₀.mul_mem hx (V₀.inv_mem hy)
    have h1 : (QuotientGroup.mk' Z) (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : x * y⁻¹ = 1 := hV0_inj (x * y⁻¹) hmem h1
    rwa [mul_inv_eq_one] at h2
  have hsubtop : Subgroup.map V₀.subtype (⊤ : Subgroup ↥V₀) = V₀ := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hy
      exact x.2
    · intro hy
      exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, trivial, rfl⟩
  have hcard_map : Nat.card (Subgroup.map (QuotientGroup.mk' Z) V₀) = 4 := by
    have hrestrict_inj : Function.Injective
        ((QuotientGroup.mk' Z).comp V₀.subtype) := by
      intro a b hab
      exact Subtype.ext (hV0_inj' a a.2 b b.2 hab)
    have h1 : Subgroup.map (QuotientGroup.mk' Z) V₀
        = Subgroup.map ((QuotientGroup.mk' Z).comp V₀.subtype) ⊤ := by
      conv_lhs => rw [← hsubtop]
      rw [Subgroup.map_map]
    rw [h1, Subgroup.card_map_of_injective hrestrict_inj, Subgroup.card_top, hV₀card]
  have hV0mapπ : Subgroup.map (QuotientGroup.mk' Z) V₀ = Vb := by
    apply Subgroup.eq_of_le_of_card_ge
    · calc Subgroup.map (QuotientGroup.mk' Z) V₀
          ≤ Subgroup.map (QuotientGroup.mk' Z) Vt := Subgroup.map_mono hV₀le
        _ = Vb := hmap
    · rw [hVb4, hcard_map]
  obtain ⟨r₀, hr₀V₀, hr₀π⟩ := Subgroup.mem_map.mp (by rw [hV0mapπ]; exact hrb)
  have hV0comm : IsMulCommutative ↥V₀ := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    have hxVb : (QuotientGroup.mk' Z) (x : ↥J) ∈ Vb :=
      Subgroup.mem_comap.mp (hV₀le x.2)
    have hyVb : (QuotientGroup.mk' Z) (y : ↥J) ∈ Vb :=
      Subgroup.mem_comap.mp (hV₀le y.2)
    have hcomm : (QuotientGroup.mk' Z) (x : ↥J) * (QuotientGroup.mk' Z) (y : ↥J)
        = (QuotientGroup.mk' Z) (y : ↥J) * (QuotientGroup.mk' Z) (x : ↥J) :=
      congrArg Subtype.val (hVb.1.is_comm.comm (⟨_, hxVb⟩ : ↥Vb) ⟨_, hyVb⟩)
    have hmem : ((x : ↥J) * (y : ↥J) * (x : ↥J)⁻¹ * (y : ↥J)⁻¹) ∈ V₀ := by
      apply V₀.mul_mem
      · apply V₀.mul_mem
        · apply V₀.mul_mem
          · exact x.2
          · exact y.2
        · exact V₀.inv_mem x.2
      · exact V₀.inv_mem y.2
    have h1 : (QuotientGroup.mk' Z)
        ((x : ↥J) * (y : ↥J) * (x : ↥J)⁻¹ * (y : ↥J)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have hw1 : (x : ↥J) * (y : ↥J) * (x : ↥J)⁻¹ * (y : ↥J)⁻¹ = 1 :=
      hV0_inj _ hmem h1
    show (x : ↥J) * (y : ↥J) = (y : ↥J) * (x : ↥J)
    calc (x : ↥J) * (y : ↥J)
        = ((x : ↥J) * (y : ↥J) * (x : ↥J)⁻¹ * (y : ↥J)⁻¹) * ((y : ↥J) * (x : ↥J)) := by
          group
      _ = 1 * ((y : ↥J) * (x : ↥J)) := by rw [hw1]
      _ = (y : ↥J) * (x : ↥J) := by rw [one_mul]
  have hV0pow : ∀ x ∈ V₀, x ^ 2 = 1 := by
    intro x hx
    have hxVb : (QuotientGroup.mk' Z) x ∈ Vb := Subgroup.mem_comap.mp (hV₀le hx)
    have h1 : (QuotientGroup.mk' Z) (x ^ 2) = 1 := by
      rw [map_pow]
      exact hVb.2 ((QuotientGroup.mk' Z) x) hxVb
    exact hV0_inj (x ^ 2) (V₀.pow_mem hx 2) h1
  have hV0 : IsElemAbelian 2 V₀ := ⟨hV0comm, hV0pow⟩
  have hr₀sq : r₀ ^ 2 = 1 := hV0pow r₀ hr₀V₀
  let V : Subgroup X := V₀.map J.subtype
  have hVcard : Nat.card V = 4 := by
    change Nat.card (V₀.map J.subtype) = 4
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective J), hV₀card]
  have hV : IsElemAbelian 2 V := map_isElemAbelian V₀ J.subtype hV0
  have hr_notC : (J.subtype r₀ : X) ∉ Subgroup.centralizer (J : Set X) := by
    intro hr
    have hr₀Z : r₀ ∈ Z := by
      rw [Subgroup.mem_center_iff]
      intro a
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hr) (J.subtype a) a.2
    have h1 : (QuotientGroup.mk' Z) r₀ = 1 := (QuotientGroup.eq_one_iff (N := Z) r₀).mpr hr₀Z
    rw [hr₀π] at h1
    exact hrb1 h1
  have hVconj : ∀ v ∈ V, v ≠ 1 → ∃ j ∈ J, v = j * (J.subtype r₀) * j⁻¹ := by
    intro v hv hv1
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    have hv₀1 : v₀ ≠ 1 := by
      intro h
      exact hv1 (by rw [h, map_one])
    have hv₀Vb : (QuotientGroup.mk' Z) v₀ ∈ Vb := Subgroup.mem_comap.mp (hV₀le hv₀)
    have hv₀πne : (QuotientGroup.mk' Z) v₀ ≠ 1 := by
      intro h
      exact hv₀1 (hV0_inj v₀ hv₀ h)
    obtain ⟨jb, hjb⟩ := hconj ((QuotientGroup.mk' Z) v₀) hv₀Vb hv₀πne
    obtain ⟨j, hjπ⟩ := QuotientGroup.mk_surjective jb
    have hjπ' : (QuotientGroup.mk' Z) j = jb := by
      simpa only [QuotientGroup.mk'_apply] using hjπ
    have hq : (QuotientGroup.mk' Z) (v₀⁻¹ * (j * r₀ * j⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [hjπ', hjb, hr₀π]
      group
    have hz : v₀⁻¹ * (j * r₀ * j⁻¹) ∈ Z := by
      have hz1 : (QuotientGroup.mk (v₀⁻¹ * (j * r₀ * j⁻¹)) : ↥J ⧸ Z) = 1 := by
        simpa only [QuotientGroup.mk'_apply] using hq
      exact (QuotientGroup.eq_one_iff (N := Z) _).mp hz1
    let w : ↥J := j * r₀ * j⁻¹
    let z : ↥J := v₀⁻¹ * w
    have hzZ : z ∈ Z := hz
    have hzcent : ∀ g : ↥J, g * z = z * g := Subgroup.mem_center_iff.mp hzZ
    have hw_eq : w = v₀ * z := by
      change j * r₀ * j⁻¹ = v₀ * (v₀⁻¹ * (j * r₀ * j⁻¹))
      group
    have hwsq : w ^ 2 = 1 := by
      have h1 : (j * r₀ * j⁻¹) ^ 2 = j * r₀ ^ 2 * j⁻¹ := conj_sq j r₀
      change (j * r₀ * j⁻¹) ^ 2 = 1
      rw [h1, hr₀sq]
      simp only [mul_one, mul_inv_cancel]
    have hzsq : z ^ 2 = 1 := by
      have h2 : (v₀ * z) ^ 2 = 1 := by rw [← hw_eq, hwsq]
      have h3 : (v₀ * z) ^ 2 = z ^ 2 := by
        rw [pow_two]
        calc (v₀ * z) * (v₀ * z) = v₀ * (z * v₀) * z := by simp only [mul_assoc]
          _ = v₀ * (v₀ * z) * z := by rw [← hzcent v₀]
          _ = v₀ * v₀ * (z * z) := by simp only [mul_assoc]
          _ = z ^ 2 := by
            rw [show v₀ * v₀ = 1 from by rw [← pow_two]; exact hV0pow v₀ hv₀, one_mul,
              pow_two]
      rw [h3] at h2
      exact h2
    have hz1 : z = 1 := center_eq_one_of_sq_eq_one hZ hzZ hzsq
    have hwv : w = v₀ := by rw [hw_eq, hz1, mul_one]
    refine ⟨J.subtype j, j.2, ?_⟩
    show (J.subtype v₀ : X) = J.subtype j * (J.subtype r₀) * (J.subtype j)⁻¹
    rw [← hwv]
    change J.subtype (j * r₀ * j⁻¹) = J.subtype j * J.subtype r₀ * (J.subtype j)⁻¹
    rw [map_mul, map_mul, map_inv]
  refine ⟨V, J.subtype r₀, ?_, ?_, hV, hVcard, hr_notC, hVconj, ⟨r₀, rfl, hr₀π⟩, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨r₀, hr₀V₀, rfl⟩
  · exact Subgroup.map_subtype_le V₀
  · change Subgroup.map (QuotientGroup.mk' Z) ((V₀.map J.subtype).comap J.subtype) = Vb
    rw [Subgroup.comap_map_eq_self_of_injective J.subtype_injective]
    exact hV0mapπ
  · intro Y hY hYN hYC hYnorm v hv y hy
    let N : Subgroup X := Subgroup.normalizer (J : Set X)
    let Yaut : Subgroup (MulAut (↥J ⧸ Z)) := (Y.subgroupOf N).map (normalizerAlpha J)
    have hYp : IsPGroup 2 Yaut := by
      have hYsub : IsPGroup 2 (Y.subgroupOf N) := by
        have h := IsPGroup.comap_of_injective hY N.subtype (Subgroup.subtype_injective N)
        rwa [Subgroup.comap_subtype] at h
      exact IsPGroup.map hYsub (normalizerAlpha J)
    have hfix : ∀ φ ∈ Yaut, φ rb = rb := by
      intro φ hφ
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hφ
      have hy'Y : (y' : X) ∈ Y := Subgroup.mem_subgroupOf.mp hy'
      have hcomm : (y' : X) * (r₀ : X) = (r₀ : X) * (y' : X) :=
        ((Subgroup.mem_centralizer_iff.mp (hYC hy'Y) (J.subtype r₀) (by simp))).symm
      have hsig : (Subgroup.normalizerMonoidHom J y') r₀ = r₀ := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcomm]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
      change normalizerAlpha J y' rb = rb
      rw [← hr₀π, normalizerAlpha_mk', hsig]
    have hnorm : ∀ c' : ↥J ⧸ Z, c' * rb = rb * c' →
        MulAut.conj c' ∈ Subgroup.normalizer (Yaut : Set (MulAut (↥J ⧸ Z))) := by
      intro c' hc'
      obtain ⟨c, hcπ⟩ := QuotientGroup.mk_surjective c'
      have hcπ' : (QuotientGroup.mk' Z) c = c' := by
        simpa only [QuotientGroup.mk'_apply] using hcπ
      have hcr : c * r₀ * c⁻¹ = r₀ := by
        have hq : (QuotientGroup.mk' Z) (c * r₀ * c⁻¹) = (QuotientGroup.mk' Z) r₀ := by
          rw [map_mul, map_mul, map_inv, hcπ', hr₀π, hc', mul_assoc, mul_inv_cancel, mul_one]
        obtain ⟨z, hzZ, hz⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hq
        have hzcent : ∀ g : ↥J, g * z = z * g := Subgroup.mem_center_iff.mp hzZ
        have hweq : c * r₀ * c⁻¹ = r₀ * z⁻¹ := eq_mul_inv_of_mul_eq hz
        have hwsq : (c * r₀ * c⁻¹) ^ 2 = 1 := by
          have h1 : (c * r₀ * c⁻¹) ^ 2 = c * r₀ ^ 2 * c⁻¹ := conj_sq c r₀
          rw [h1, hr₀sq]
          simp only [mul_one, mul_inv_cancel]
        have h2 : (r₀ * z⁻¹) ^ 2 = 1 := by rw [← hweq]; exact hwsq
        have h3 : (r₀ * z⁻¹) ^ 2 = (z ^ 2)⁻¹ := by
          rw [pow_two]
          calc (r₀ * z⁻¹) * (r₀ * z⁻¹)
              = r₀ * (z⁻¹ * r₀) * z⁻¹ := by simp only [mul_assoc]
            _ = r₀ * (r₀ * z⁻¹) * z⁻¹ := by
                rw [← Subgroup.mem_center_iff.mp (Z.inv_mem hzZ) r₀]
            _ = r₀ * r₀ * (z⁻¹ * z⁻¹) := by simp only [mul_assoc]
            _ = z⁻¹ * z⁻¹ := by
                rw [show r₀ * r₀ = 1 from by rw [← pow_two]; exact hr₀sq, one_mul]
            _ = (z ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
        rw [h3] at h2
        have hzsq : z ^ 2 = 1 := by simpa using congrArg Inv.inv h2
        rw [hweq, center_eq_one_of_sq_eq_one hZ hzZ hzsq, inv_one, mul_one]
      have hcX : (c : X) * (r₀ : X) = (r₀ : X) * (c : X) := by
        have h := congrArg (fun a : ↥J => (a : X)) hcr
        change ((c : X) * (r₀ : X) * (c : X)⁻¹) = (r₀ : X) at h
        calc (c : X) * (r₀ : X)
            = ((c : X) * (r₀ : X) * (c : X)⁻¹) * (c : X) := by group
          _ = (r₀ : X) * (c : X) := by rw [h]
      have hYnormc : (c : X) ∈ Subgroup.normalizer (Y : Set X) := hYnorm (c : X) c.2 hcX
      let cN : ↥N := ⟨(c : X), Subgroup.le_normalizer c.2⟩
      have halpha_c : normalizerAlpha J cN = MulAut.conj c' := by
        dsimp only [cN]
        rw [normalizerAlpha_conj, hcπ']
      rw [Subgroup.mem_normalizer_iff]
      intro φ
      constructor
      · intro hφ
        obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hφ
        have hmem : cN * n * cN⁻¹ ∈ Y.subgroupOf N := by
          rw [Subgroup.mem_subgroupOf]
          have hn' : (n : X) ∈ Y := Subgroup.mem_subgroupOf.mp hn
          have h := (Subgroup.mem_normalizer_iff.mp hYnormc) (n : X)
          simpa using (h.mp hn')
        refine Subgroup.mem_map.mpr ⟨cN * n * cN⁻¹, hmem, ?_⟩
        rw [← halpha_c, ← map_mul, ← map_inv, ← map_mul]
      · intro hφ
        obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hφ
        have hcXinv : (c : X)⁻¹ * (r₀ : X) = (r₀ : X) * (c : X)⁻¹ := by
          have hr2 : (r₀ : X) * (r₀ : X) = 1 := by
            change (J.subtype r₀ : X) * (J.subtype r₀ : X) = 1
            rw [← map_mul, ← pow_two, hr₀sq, map_one]
          have hrinv : (r₀ : X)⁻¹ = (r₀ : X) := inv_eq_of_mul_eq_one_left hr2
          have hinv := congrArg Inv.inv hcX
          simp only [mul_inv_rev] at hinv
          rw [hrinv] at hinv
          exact hinv.symm
        have hYnormcinv : (c : X)⁻¹ ∈ Subgroup.normalizer (Y : Set X) :=
          hYnorm ((c : X)⁻¹) (J.inv_mem c.2) hcXinv
        have hmem : cN⁻¹ * m * cN ∈ Y.subgroupOf N := by
          rw [Subgroup.mem_subgroupOf]
          have hm' : (m : X) ∈ Y := Subgroup.mem_subgroupOf.mp hm
          have h := (Subgroup.mem_normalizer_iff.mp hYnormcinv) (m : X)
          simpa using (h.mp hm')
        refine Subgroup.mem_map.mpr ⟨cN⁻¹ * m * cN, hmem, ?_⟩
        have h1 : normalizerAlpha J (cN⁻¹ * m * cN)
            = (normalizerAlpha J cN)⁻¹ * normalizerAlpha J m * normalizerAlpha J cN := by
          rw [map_mul, map_mul, map_inv]
        rw [h1, halpha_c, hmeq]
        group
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    have hyN : y ∈ N := hYN hy
    let yN : ↥N := ⟨y, hyN⟩
    have hyNsub : yN ∈ Y.subgroupOf N := Subgroup.mem_subgroupOf.mpr hy
    have hvVb : (QuotientGroup.mk' Z) v₀ ∈ Vb := Subgroup.mem_comap.mp (hV₀le hv₀)
    have hyaut : normalizerAlpha J yN ∈ Yaut :=
      Subgroup.mem_map.mpr ⟨yN, hyNsub, rfl⟩
    have hK1app : normalizerAlpha J yN ((QuotientGroup.mk' Z) v₀)
        * ((QuotientGroup.mk' Z) v₀)⁻¹ ∈ Subgroup.zpowers rb :=
      hK1 Yaut hYp hfix hnorm ((QuotientGroup.mk' Z) v₀) hvVb (normalizerAlpha J yN) hyaut
    obtain ⟨k₀, hk₀⟩ := (Subgroup.mem_zpowers_iff).mp hK1app
    have hq : (QuotientGroup.mk' Z) ((Subgroup.normalizerMonoidHom J yN) v₀ * v₀⁻¹)
        = (QuotientGroup.mk' Z) (r₀ ^ k₀) := by
      rw [map_mul, map_inv, ← normalizerAlpha_mk', ← hk₀, map_zpow, hr₀π]
    obtain ⟨z', hz'Z, hz'⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hq
    let a : ↥J := (Subgroup.normalizerMonoidHom J yN) v₀ * v₀⁻¹
    have haz : a * z' = r₀ ^ k₀ := by simpa only [a] using hz'
    have ha_inv : a⁻¹ = r₀ ^ (-k₀) * z' := by
      have ha : a = r₀ ^ k₀ * z'⁻¹ := eq_mul_inv_of_mul_eq haz
      rw [ha, mul_inv_rev, inv_inv, zpow_neg]
      exact (Subgroup.mem_center_iff.mp hz'Z ((r₀ ^ k₀)⁻¹)).symm
    have hva : (J.subtype v₀ : X) * y * (J.subtype v₀)⁻¹ * y⁻¹ = J.subtype a⁻¹ := by
      have h1 : (J.subtype a : X) = (y * (J.subtype v₀) * y⁻¹) * (J.subtype v₀)⁻¹ := by
        change J.subtype ((Subgroup.normalizerMonoidHom J yN) v₀ * v₀⁻¹)
          = (y * J.subtype v₀ * y⁻¹) * (J.subtype v₀)⁻¹
        rw [map_mul, map_inv, Subgroup.subtype_apply,
          Subgroup.normalizerMonoidHom_apply_apply_coe]
        rfl
      rw [map_inv, h1]
      group
    refine ⟨-k₀, J.subtype z', ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      let b : ↥J := ⟨h, hh⟩
      change J.subtype b * J.subtype z' = J.subtype z' * J.subtype b
      simpa using congrArg (Subgroup.subtype J) (Subgroup.mem_center_iff.mp hz'Z b)
    · have hgoal : (J.subtype v₀ : X) * y * (J.subtype v₀)⁻¹ * y⁻¹
          = (J.subtype r₀) ^ (-k₀) * J.subtype z' := by
        rw [hva, ha_inv, map_mul, map_zpow]
      exact hgoal

end CFSG.StandardType.K1Lift
