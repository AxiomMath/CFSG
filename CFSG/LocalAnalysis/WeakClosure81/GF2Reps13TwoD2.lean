module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoD1
public import CFSG.GroupTheory.IndexFourQuotientKernel
public import CFSG.Quasithin.EmptyFaithful.A38c16BlocksIndep

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {t : MulAut W} {P : Subgroup (MulAut W)}

open CFSG.Quasithin.SzN31

attribute [local irreducible] zmodMulEquivOfGenerator

private theorem w16g_zpowers_eq_one_or_self {A : Type*} [Group A] {t : A} (ht : t * t = 1)
    {b : A} (hb : b ∈ Subgroup.zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : t ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, pow_two]
    exact ht
  have hmod := zpow_eq_zpow_emod k h2
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [hmod, h, zpow_zero]
  · right; rw [hmod, h, zpow_one]

private theorem w16g_conj_commutator_self_inv {A : Type*} [Group A] {t a : A}
    (htt : t * t = 1) : t * ⁅a, t⁆ * t⁻¹ = ⁅a, t⁆⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have h1 : t * ⁅a, t⁆ * t⁻¹ = t * a * t * a⁻¹ := by
    rw [commutatorElement_def, htinv]
    calc t * (a * t * a⁻¹ * t) * t = (t * a * t * a⁻¹) * (t * t) := by group
      _ = (t * a * t * a⁻¹) * 1 := by rw [htt]
      _ = t * a * t * a⁻¹ := mul_one _
  have h2 : ⁅a, t⁆⁻¹ = t * a * t * a⁻¹ := by
    rw [commutatorElement_inv, commutatorElement_def, htinv]
  rw [h1, h2]

private theorem w16g_exp_three_of_inverts_center {Q : Type} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 27) (hnc : ∃ u v : Q, u * v ≠ v * u) (σ : Q →* Q)
    (hσ : ∀ x, σ (σ x) = x) (hZfix : ∀ z ∈ Subgroup.center Q, σ z = z)
    (hinv : ∀ x : Q, σ x * x ∈ Subgroup.center Q) : ∀ x : Q, x ^ 3 = 1 := by
  intro x
  have hc := hinv x
  have hx3 := SmD6Grp.cube_mem_center hQ hnc x
  have hc3 := SmD6Grp.pow_three_eq_one_of_mem_center hQ hnc hc
  have hfix3 : σ (x ^ 3) = x ^ 3 := hZfix _ hx3
  have h1 : (σ x) ^ 3 = x ^ 3 := by rw [← map_pow, hfix3]
  have h2 : (σ x) ^ 3 = (x ^ 3)⁻¹ := by
    have hx : σ x = (σ x * x) * x⁻¹ := by group
    rw [hx, SmD6Grp.mul_pow_three hQ hnc, hc3, one_mul, inv_pow]
  have h3 : x ^ 3 = (x ^ 3)⁻¹ := h1.symm.trans h2
  have h6 : x ^ 6 = 1 := by
    have h33 : x ^ 3 * x ^ 3 = 1 := by
      nth_rewrite 2 [h3]
      exact mul_inv_cancel _
    rwa [← pow_add] at h33
  have hord : orderOf x ∣ 3 := by
    have h27 : orderOf x ∣ 27 := by rw [← hQ]; exact orderOf_dvd_natCard x
    have h6' : orderOf x ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr h6
    have hg := Nat.dvd_gcd h27 h6'
    norm_num at hg
    exact hg
  exact orderOf_dvd_iff_pow_eq_one.mp hord

private theorem w16g_inverts_center_quotient {W : Type} [CommGroup W] [Finite W]
    {t : MulAut W} {P : Subgroup (MulAut W)} (htt : t * t = 1)
    (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ = P)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z)
    (hQcomm : ∀ a b : ↥P ⧸ Subgroup.center ↥P, a * b = b * a) :
    ∃ σ : ↥P →* ↥P, (∀ x, (σ x : MulAut W) = t * x * t⁻¹) ∧ (∀ x, σ (σ x) = x) ∧
      (∀ z : ↥P, z ∈ Subgroup.center ↥P → σ z = z) ∧
      (∀ x : ↥P, σ x * x ∈ Subgroup.center ↥P) := by
  classical
  obtain ⟨σ, hσ⟩ := SmD6Grp.exists_conj_hom (G := MulAut W) t hn
  have hσσ : ∀ x : ↥P, σ (σ x) = x := by
    intro x
    apply Subtype.ext
    rw [hσ, hσ]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
    rw [htinv]
    calc t * (t * (x : MulAut W) * t) * t
        = (t * t) * (x : MulAut W) * (t * t) := by group
      _ = x := by rw [htt]; group
  have hZfix : ∀ z : ↥P, z ∈ Subgroup.center ↥P → σ z = z := by
    intro z hz
    apply Subtype.ext
    rw [hσ]
    exact hZ z z.2 (fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩))
  let Z := Subgroup.center ↥P
  have hσZ : Z ≤ Z.comap σ := by
    intro z hz
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    calc g * σ z = σ (σ g) * σ z := by rw [hσσ]
      _ = σ (σ g * z) := (map_mul σ (σ g) z).symm
      _ = σ (z * σ g) := by rw [hz (σ g)]
      _ = σ z * σ (σ g) := map_mul σ z (σ g)
      _ = σ z * g := by rw [hσσ]
  let φ : ↥P ⧸ Z →* ↥P ⧸ Z :=
    { toFun := fun q => QuotientGroup.map Z Z σ hσZ q * q
      map_one' := by simp
      map_mul' := by
        intro a b
        show QuotientGroup.map Z Z σ hσZ (a * b) * (a * b) =
          (QuotientGroup.map Z Z σ hσZ a * a) * (QuotientGroup.map Z Z σ hσZ b * b)
        rw [map_mul]
        calc QuotientGroup.map Z Z σ hσZ a * QuotientGroup.map Z Z σ hσZ b * (a * b)
            = QuotientGroup.map Z Z σ hσZ a
                * (QuotientGroup.map Z Z σ hσZ b * a) * b := by group
          _ = QuotientGroup.map Z Z σ hσZ a
                * (a * QuotientGroup.map Z Z σ hσZ b) * b := by
                rw [hQcomm (QuotientGroup.map Z Z σ hσZ b) a]
          _ = (QuotientGroup.map Z Z σ hσZ a * a)
                * (QuotientGroup.map Z Z σ hσZ b * b) := by group }
  have hφπ : ∀ x : ↥P, φ (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z (σ x * x) := by
    intro x
    show QuotientGroup.map Z Z σ hσZ (QuotientGroup.mk' Z x) * QuotientGroup.mk' Z x
        = QuotientGroup.mk' Z (σ x * x)
    rw [QuotientGroup.map_mk']
    exact (map_mul (QuotientGroup.mk' Z) (σ x) x).symm
  let B : Subgroup (MulAut W) := (φ.ker.comap (QuotientGroup.mk' Z)).map P.subtype
  have hgen : ⁅P, Subgroup.zpowers t⁆ ≤ B := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases w16g_zpowers_eq_one_or_self htt hb with hb1 | hbt
    · rw [hb1]; simpa using B.one_mem
    · rw [hbt]
      apply Subgroup.mem_map.mpr
      have hmem : ⁅a, t⁆ ∈ P := by
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
        have hmem1 : t * a⁻¹ * t⁻¹ ∈ P := hn a⁻¹ (P.inv_mem ha)
        rw [commutatorElement_def, htinv]
        rw [htinv] at hmem1
        simpa [mul_assoc] using P.mul_mem ha hmem1
      refine ⟨⟨⁅a, t⁆, hmem⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap, MonoidHom.mem_ker]
      have hσx : σ ⟨⁅a, t⁆, hmem⟩ = (⟨⁅a, t⁆, hmem⟩ : ↥P)⁻¹ := by
        apply Subtype.ext
        rw [hσ, Subgroup.coe_inv]
        exact w16g_conj_commutator_self_inv (a := a) htt
      rw [hφπ, hσx, inv_mul_cancel, map_one]
  have hPB : P ≤ B := hc ▸ hgen
  have hBeq : B = P := le_antisymm (Subgroup.map_subtype_le _) hPB
  have hkerTop : φ.ker.comap (QuotientGroup.mk' Z) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hBeq
  refine ⟨σ, hσ, hσσ, hZfix, fun x => ?_⟩
  have hx : x ∈ φ.ker.comap (QuotientGroup.mk' Z) := by
    rw [hkerTop]; exact Subgroup.mem_top x
  rw [Subgroup.mem_comap, MonoidHom.mem_ker] at hx
  have hφ1 : φ (QuotientGroup.mk' Z x) = 1 := hx
  rw [hφπ x] at hφ1
  rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hφ1

private theorem w16g_mem_stabSub_of_mapsTo {V : Type*} [CommGroup V] [Finite V] {U : Subgroup V}
    {x : MulAut V} (h : ∀ u ∈ U, x u ∈ U) : x ∈ stabSub U := by
  rw [mem_stabSub]
  have hmap : U.map x.toMonoidHom = U := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      exact h u hu
    · rw [Subgroup.card_map_of_injective (K := U) x.injective]
  intro u
  constructor
  · intro hu
    rw [← hmap] at hu
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hu
    rwa [x.injective hwx] at hw
  · exact h u

private theorem w16g_shift_unique {W : Type*} [CommGroup W] [Finite W] {U : Fin 3 → Subgroup W}
    (hind : iSupIndep U) (hrk : ∀ i, rk ↥(U i) = 2) {x : MulAut W} {d e : Fin 3}
    (hd : ∀ i, ∀ u ∈ U i, x u ∈ U (i + d)) (he : ∀ i, ∀ u ∈ U i, x u ∈ U (i + e)) :
    d = e := by
  have hUi_ne : ∀ i, U i ≠ ⊥ := by
    intro i hbot
    have h2 := hrk i
    rw [hbot, rk_bot] at h2
    norm_num at h2
  have hkey : ∀ i : Fin 3, ¬ Disjoint (U (i + d)) (U (i + e)) := by
    intro i hdis
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hUi_ne i)
    have h1 : x u.1 ∈ U (i + d) := hd i u.1 u.2
    have h2 : x u.1 ∈ U (i + e) := he i u.1 u.2
    have h3 : x u.1 ∈ U (i + d) ⊓ U (i + e) := ⟨h1, h2⟩
    rw [hdis.eq_bot, Subgroup.mem_bot] at h3
    exact hu1 (Subtype.ext (x.injective (h3.trans (map_one x).symm)))
  have hadd : ∀ i : Fin 3, i + d = i + e := by
    intro i
    by_contra hne
    exact hkey i (hind.pairwiseDisjoint hne)
  exact add_left_cancel (hadd 0)

private theorem w16g_mem_zpowers_of_card_le_six {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G ≤ 6) {z x : G} (hz : orderOf z = 3) (hx : orderOf x ∣ 3) :
    x ∈ Subgroup.zpowers z := by
  rcases eq_or_ne x 1 with hx1 | hx1
  · rw [hx1]; exact Subgroup.one_mem _
  have hx3 : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hx with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hcardx : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  have hcardz : Nat.card ↥(Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz]
  by_contra hmem
  have hne : Subgroup.zpowers x ≠ Subgroup.zpowers z := by
    intro h
    exact hmem (h ▸ Subgroup.mem_zpowers x)
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers z = ⊥ := by
    by_contra hbot
    have hcard : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers z) ≠ 1 := fun h1 =>
      hbot ((Subgroup.card_eq_one).mp h1)
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers z) ∣ 3 := by
      rw [← hcardx]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers z) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hcard
      · exact h
    have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers z = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcardx])
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers z := heq ▸ inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardz, hcardx]))
  let f : ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers z) → G :=
    fun p => (p.1 : G) * (p.2 : G)
  have hinj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ heq
    have heq' : (a : G) * (b : G) = (c : G) * (d : G) := heq
    have h1 : (c : G)⁻¹ * (a : G) = (d : G) * (b : G)⁻¹ := by
      calc (c : G)⁻¹ * (a : G) = (c : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
        _ = (c : G)⁻¹ * ((c : G) * (d : G)) * (b : G)⁻¹ := by rw [heq']
        _ = (d : G) * (b : G)⁻¹ := by group
    have hm1 : (c : G)⁻¹ * (a : G) ∈ Subgroup.zpowers x :=
      (Subgroup.zpowers x).mul_mem ((Subgroup.zpowers x).inv_mem hc) ha
    have hm2 : (c : G)⁻¹ * (a : G) ∈ Subgroup.zpowers z := by
      rw [h1]
      exact (Subgroup.zpowers z).mul_mem hd ((Subgroup.zpowers z).inv_mem hb)
    have hbotm : (c : G)⁻¹ * (a : G) ∈ (⊥ : Subgroup G) := by
      rw [← hinf]; exact ⟨hm1, hm2⟩
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hbotm
    have hb' : (b : G) = (d : G) := by
      rw [hbotm] at heq'
      exact mul_left_cancel heq'
    refine Prod.ext (Subtype.ext hbotm.symm) (Subtype.ext hb')
  have hle := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, hcardx, hcardz] at hle
  omega

private theorem w16g_hom_eq_one_of_generated
    {G A : Type*} [Group G] [CommGroup A]
    {N : Subgroup G} [hN : N.Normal] (s : N →* A)
    (h2 : ∀ a : A, a * a = 1 → a = 1)
    {τ : G →* G} (hττ : ∀ g : G, τ (τ g) = g)
    (hτN : ∀ n : N, τ (n : G) ∈ N)
    (hτs : ∀ n : N, s ⟨τ (n : G), hτN n⟩ = s n)
    (hinv : ∀ (g : G) (n : N), s ⟨g * (n : G) * g⁻¹, hN.conj_mem (n : G) n.2 g⟩ = s n)
    {y : G} (hsplit : ∀ g : G, ∃ n : N, ∃ i : ℤ, g = (n : G) * y ^ i)
    (hgen : ∀ g : G, g ∈ Subgroup.closure {x : G | ∃ h : G, x = h * (τ h)⁻¹}) :
    ∀ n : N, s n = 1 := by
  classical
  let K : Subgroup G := s.ker.map N.subtype
  have hKN : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_map]
    exact ⟨⟨g * (m : G) * g⁻¹, hN.conj_mem (m : G) m.2 g⟩, by
      rw [MonoidHom.mem_ker, hinv g m]
      exact MonoidHom.mem_ker.mp hm, rfl⟩
  haveI : K.Normal := hKN
  have hNK : ⁅N, ⊤⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hconj : b * a⁻¹ * b⁻¹ ∈ N := hN.conj_mem a⁻¹ (N.inv_mem ha) b
    have hmem : ⁅a, b⁆ ∈ N := by
      have h := N.mul_mem ha hconj
      simpa [commutatorElement_def, mul_assoc] using h
    rw [Subgroup.mem_map]
    refine ⟨⟨⁅a, b⁆, hmem⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hprod : (⟨⁅a, b⁆, hmem⟩ : N) = ⟨a, ha⟩ * ⟨b * a⁻¹ * b⁻¹, hconj⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    rw [hprod, map_mul, hinv b ⟨a⁻¹, N.inv_mem ha⟩]
    have hcoe : (⟨a⁻¹, N.inv_mem ha⟩ : N) = (⟨a, ha⟩ : N)⁻¹ := Subtype.ext rfl
    rw [hcoe, map_inv s ⟨a, ha⟩]
    exact mul_inv_cancel _
  let D : Subgroup G :=
    { carrier := {x : G | ∀ g : G, ⁅x, g⁆ ∈ K}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact K.mul_mem (hKN.conj_mem (⁅b, g⁆) (hb g) a) (ha g)
      inv_mem' := by
        intro a ha g
        rw [commutatorElement_inv_left]
        have h1 : ⁅g, a⁆ ∈ K := by
          have h := K.inv_mem (ha g)
          rwa [commutatorElement_inv] at h
        simpa using hKN.conj_mem (⁅g, a⁆) h1 a⁻¹ }
  have hyD : y ∈ D := by
    intro g
    obtain ⟨n, i, rfl⟩ := hsplit g
    have h1 : ⁅y, (n : G)⁆ ∈ K := by
      have h := hNK
      rw [Subgroup.commutator_le] at h
      simpa using K.inv_mem (h (n : G) n.2 y (Subgroup.mem_top y))
    have h2 : ⁅y, y ^ i⁆ = 1 := (Commute.zpow_right (Commute.refl y) i).commutator_eq
    rw [commutatorElement_mul_right_eq_mul_conj, h2]
    simpa using h1
  have hYN : ⁅Subgroup.zpowers y, ⊤⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (Subgroup.zpowers_le.mpr hyD ha) b
  have hTop : N ⊔ Subgroup.zpowers y = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨n, i, rfl⟩ := hsplit g
    exact Subgroup.mul_mem_sup n.2 (Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩)
  have hGG : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ K := by
    have hEq : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⁅N, ⊤⁆ ⊔ ⁅Subgroup.zpowers y, ⊤⁆ := by
      have h := Subgroup.commutator_sup_right N (Subgroup.zpowers y) (⊤ : Subgroup G)
      rwa [hTop] at h
    rw [hEq]
    exact sup_le hNK hYN
  haveI : IsMulCommutative (G ⧸ K) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
    simpa [_root_.commutator_def] using hGG
  have hτK : K ≤ K.comap τ := by
    intro k hk
    rw [Subgroup.mem_comap]
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_map]
    exact ⟨⟨τ (m : G), hτN m⟩, by
      rw [MonoidHom.mem_ker, hτs m]
      exact MonoidHom.mem_ker.mp hm, rfl⟩
  let τbar : G ⧸ K →* G ⧸ K := QuotientGroup.map K K τ hτK
  have hτbar : ∀ g : G, τbar (g : G ⧸ K) = (τ g : G ⧸ K) :=
    fun g => QuotientGroup.map_mk K K τ hτK g
  have hτbar' : ∀ g : G, τbar (QuotientGroup.mk' K g) = QuotientGroup.mk' K (τ g) :=
    fun g => hτbar g
  have hττbar : ∀ q : G ⧸ K, τbar (τbar q) = q := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    rw [hτbar, hτbar, hττ]
  have hgenQ : (⊤ : Subgroup (G ⧸ K)) ≤
      Subgroup.closure {x : G ⧸ K | ∃ h : G ⧸ K, x = h * (τbar h)⁻¹} := by
    have hS : Subgroup.closure {x : G | ∃ h : G, x = h * (τ h)⁻¹} = ⊤ := by
      rw [eq_top_iff]
      intro g _
      exact hgen g
    have hmap := MonoidHom.map_closure (QuotientGroup.mk' K)
      {x : G | ∃ h : G, x = h * (τ h)⁻¹}
    rw [hS, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] at hmap
    have hsub : (QuotientGroup.mk' K) '' {x : G | ∃ h : G, x = h * (τ h)⁻¹} ⊆
        {x : G ⧸ K | ∃ h : G ⧸ K, x = h * (τbar h)⁻¹} := by
      rintro x ⟨s, hs, hx⟩
      obtain ⟨h, rfl⟩ := hs
      rw [← hx]
      exact ⟨QuotientGroup.mk' K h, by rw [map_mul, map_inv, hτbar']⟩
    calc (⊤ : Subgroup (G ⧸ K))
        = Subgroup.closure ((QuotientGroup.mk' K) '' {x : G | ∃ h, x = h * (τ h)⁻¹}) := hmap
      _ ≤ Subgroup.closure {x : G ⧸ K | ∃ h, x = h * (τbar h)⁻¹} := Subgroup.closure_mono hsub
  let Afix : Subgroup (G ⧸ K) :=
    { carrier := {q : G ⧸ K | τbar q = q⁻¹}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        show τbar (a * b) = (a * b)⁻¹
        rw [map_mul, ha, hb, mul_inv_rev, mul_comm']
      inv_mem' := by
        intro a ha
        show τbar a⁻¹ = (a⁻¹)⁻¹
        rw [map_inv, ha, inv_inv] }
  have hAfix : Afix = ⊤ := by
    rw [eq_top_iff]
    refine le_trans hgenQ ?_
    rw [Subgroup.closure_le]
    rintro x ⟨h, rfl⟩
    show τbar (h * (τbar h)⁻¹) = (h * (τbar h)⁻¹)⁻¹
    rw [map_mul, map_inv, hττbar, mul_inv_rev, inv_inv]
  intro n
  have hqf : ∀ q : G ⧸ K, τbar q = q⁻¹ := by
    intro q
    have hq : q ∈ Afix := by rw [hAfix]; exact Subgroup.mem_top q
    exact hq
  have hmemK : (τ (n : G))⁻¹ * (n : G) ∈ K := by
    rw [Subgroup.mem_map]
    refine ⟨⟨(τ (n : G))⁻¹ * (n : G), N.mul_mem (N.inv_mem (hτN n)) n.2⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    have hprod : (⟨(τ (n : G))⁻¹ * (n : G), N.mul_mem (N.inv_mem (hτN n)) n.2⟩ : N) =
        ⟨(τ (n : G))⁻¹, N.inv_mem (hτN n)⟩ * n := Subtype.ext rfl
    have hcoe : (⟨(τ (n : G))⁻¹, N.inv_mem (hτN n)⟩ : N) =
        (⟨τ (n : G), hτN n⟩ : N)⁻¹ := Subtype.ext rfl
    rw [hprod, map_mul, hcoe, map_inv, hτs n]
    exact inv_mul_cancel _
  have hfixn : QuotientGroup.mk' K (τ (n : G)) = QuotientGroup.mk' K (n : G) := by
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨_, hmemK, by group⟩
  have hninv : (((n : G) : G ⧸ K)) = ((((n : G)) : G ⧸ K))⁻¹ := by
    rw [← hqf (((n : G)) : G ⧸ K)]
    exact hfixn.symm
  have hsq : (n : G) ^ 2 ∈ K := by
    have h : (((n : G) ^ 2 : G) : G ⧸ K) = 1 := by
      rw [QuotientGroup.mk_pow, pow_two]
      nth_rewrite 2 [hninv]
      rw [mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff ((n : G) ^ 2)).mp h
  obtain ⟨m, hm, hmeq⟩ := Subgroup.mem_map.mp hsq
  have hm1 : s m = 1 := by simpa using MonoidHom.mem_ker.mp hm
  have hm2 : m = n ^ 2 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hmeq
  refine h2 (s n) ?_
  calc s n * s n = (s n) ^ 2 := (pow_two (s n)).symm
    _ = s (n ^ 2) := (map_pow s n 2).symm
    _ = s m := by rw [hm2]
    _ = 1 := hm1

private theorem w16g_prod_fin_three_add {M : Type*} [CommMonoid M] (f : Fin 3 → M) (c : Fin 3) :
    (∏ i : Fin 3, f (i + c)) = ∏ i : Fin 3, f i := by
  have hinj : ∀ a b : Fin 3, a + c = b + c → a = b := by
    intro a b h
    exact add_left_cancel (by rwa [add_comm a c, add_comm b c] at h)
  have hbij : Function.Bijective (fun i : Fin 3 => i + c) :=
    Finite.injective_iff_bijective.mp hinj
  have h := Finset.prod_image (f := f) (g := fun i : Fin 3 => i + c) (s := Finset.univ)
    (fun a _ b _ h => hinj a b h)
  rw [Finset.image_univ_of_surjective hbij.surjective] at h
  exact h.symm

theorem w16h_central_card_le (h : Cfg132 t P) {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3)
    (hzc : ∀ y ∈ P, y * z = z * y) (hzt : t * z * t⁻¹ = z) (hfix : ∀ u : W, z u = u → u = 1)
    {U : Fin 3 → Subgroup W} (hind : iSupIndep U) (hsup : (⨆ i, U i) = ⊤)
    (hrk : ∀ i, rk ↥(U i) = 2) (hzU : ∀ i, ∀ u ∈ U i, z u ∈ U i)
    (hP : ∀ x ∈ P, ∃ c : Fin 3, ∀ i, ∀ u ∈ U i, x u ∈ U (i + c))
    (hy : ∃ y ∈ P, ∀ i, ∀ u ∈ U i, y u ∈ U (i + 1))
    (htU : ∃ σ : Equiv.Perm (Fin 3), ∀ i, ∀ u ∈ U i, t u ∈ U (σ i)) :
    Nat.card P ≤ 27 := by
  classical
  haveI : Finite (W → W) := inferInstance
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W))
      (fun f g h => MulEquiv.ext (fun w => congrFun h w))
  haveI : Finite ↥P := Subtype.finite
  have hUi_ne : ∀ i, U i ≠ ⊥ := by
    intro i hbot
    have h2 := hrk i
    rw [hbot, rk_bot] at h2
    norm_num at h2
  let c : ↥P → Fin 3 := fun x => Classical.choose (hP x x.2)
  have hc_spec : ∀ x : ↥P, ∀ i, ∀ u ∈ U i, (x : MulAut W) u ∈ U (i + c x) := fun x =>
    Classical.choose_spec (hP x x.2)
  have hc_mul : ∀ x y : ↥P, c (x * y) = c x + c y := by
    intro x y
    apply w16g_shift_unique hind hrk (d := c (x * y)) (e := c x + c y)
    · exact hc_spec (x * y)
    · intro i u hu
      have hy1 : (y : MulAut W) u ∈ U (i + c y) := hc_spec y i u hu
      have hx1 : (x : MulAut W) ((y : MulAut W) u) ∈ U ((i + c y) + c x) :=
        hc_spec x (i + c y) ((y : MulAut W) u) hy1
      have heq : (i + c y) + c x = i + (c x + c y) := by
        rw [add_assoc, add_comm (c y) (c x)]
      rwa [heq] at hx1
  have hc_one : c 1 = 0 := by
    apply w16g_shift_unique hind hrk (d := c 1) (e := 0)
    · exact hc_spec 1
    · intro i u hu
      simpa using hu
  let cH : ↥P →* Multiplicative (ZMod 3) :=
    { toFun := fun x => Multiplicative.ofAdd (c x)
      map_one' := by rw [hc_one]; rfl
      map_mul' := by intro x y; rw [hc_mul]; rfl }
  let P₁ : Subgroup ↥P := cH.ker
  have hP₁_stab : ∀ i, P₁.map P.subtype ≤ stabSub (U i) := by
    intro i x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    apply w16g_mem_stabSub_of_mapsTo
    intro u hu
    have hcx : c y = 0 := hy
    have h1 := hc_spec y i u hu
    rwa [hcx, add_zero] at h1
  have hquot_le : Nat.card (↥P ⧸ P₁) ≤ 3 := by
    have heq : Nat.card (↥P ⧸ P₁) = Nat.card cH.range := by
      change Nat.card (↥P ⧸ cH.ker) = Nat.card cH.range
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange cH).toEquiv
    rw [heq]
    calc Nat.card cH.range ≤ Nat.card (Multiplicative (ZMod 3)) :=
          Subgroup.card_le_card_group _
      _ = 3 := by simp [Nat.card_zmod]
  have hcard_eq : Nat.card ↥P = Nat.card (↥P ⧸ P₁) * Nat.card P₁ :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup P₁
  have hP₁_le : Nat.card P₁ ≤ 9 := by
    classical
    obtain ⟨k, hk⟩ := h.hP.exists_card_eq
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, pow_zero] at hk
        exact absurd ((Subgroup.card_eq_one).mp hk) h.hne
      · exact hpos
    have hUcard : ∀ i, Nat.card ↥(U i) = 4 := by
      intro i
      rw [card_eq_two_pow h.hW (U i), hrk i]
      norm_num
    have hAut : ∀ i, Nat.card (MulAut ↥(U i)) ∣ 6 := fun i =>
      CFSG.GroupTheory.card_mulAut_dvd_six_of_card_eq_four (hUcard i)
    have hAutLe : ∀ i, Nat.card (MulAut ↥(U i)) ≤ 6 := fun i =>
      Nat.le_of_dvd (by norm_num) (hAut i)
    have hzpStab : ∀ i, Subgroup.zpowers z ≤ stabSub (U i) := fun i =>
      Subgroup.zpowers_le.mpr (w16g_mem_stabSub_of_mapsTo (hzU i))
    let zP : ↥P := ⟨z, hzP⟩
    have hzP₁ : zP ∈ P₁ := by
      rw [MonoidHom.mem_ker]
      have hshift : c zP = 0 :=
        w16g_shift_unique hind hrk (d := c zP) (e := 0) (hc_spec zP)
          (fun i u hu => by simpa using hzU i u hu)
      show Multiplicative.ofAdd (c zP) = 1
      rw [hshift]
      rfl
    let z₁ : P₁ := ⟨zP, hzP₁⟩
    have hz₁ord : orderOf z₁ = 3 := by
      have h1 : orderOf (z₁ : ↥P) = orderOf z₁ := Subgroup.orderOf_coe z₁
      have h2 : orderOf (zP : MulAut W) = orderOf zP := Subgroup.orderOf_coe zP
      rw [← h1]
      show orderOf zP = 3
      rw [← h2]
      exact hz3
    let resAt : ∀ i, P₁ →* MulAut ↥(U i) := fun i =>
      { toFun := fun x =>
          resAut (U i) ⟨(x : ↥P).1, hP₁_stab i (Subgroup.mem_map_of_mem P.subtype x.2)⟩
        map_one' := by ext u; rfl
        map_mul' := by intro x y; ext u; rfl }
    have hres_eq : ∀ (i : Fin 3) (x : P₁),
        resAt i x = resAut (U i) ⟨(x : ↥P).1,
          hP₁_stab i (Subgroup.mem_map_of_mem P.subtype x.2)⟩ := fun i x => rfl
    have hzres : ∀ i, orderOf (resAt i z₁) = 3 := by
      intro i
      have hdvd : orderOf (resAt i z₁) ∣ 3 := by
        rw [← hz₁ord]
        exact orderOf_map_dvd (resAt i) z₁
      have hne : resAt i z₁ ≠ 1 := by
        intro h1
        obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hUi_ne i)
        have hfixu : z (u : W) = (u : W) := by
          have h2 : ((resAt i z₁ u : ↥(U i)) : W) = (u : W) := by
            rw [h1]; rfl
          rwa [show ((resAt i z₁ u : ↥(U i)) : W) = z (u : W) from rfl] at h2
        exact hu (Subtype.ext (hfix (u : W) hfixu))
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hne
      · exact h'
    have hresOrd : ∀ (i : Fin 3) (x : P₁), orderOf (resAt i x) ∣ 3 := by
      intro i x
      have h6 : orderOf (resAt i x) ∣ 6 :=
        (orderOf_dvd_natCard (resAt i x)).trans (hAut i)
      have h3k : orderOf (resAt i x) ∣ 3 ^ k := by
        refine (orderOf_map_dvd (resAt i) x).trans ?_
        refine (orderOf_dvd_natCard x).trans ?_
        rw [← hk]
        have htop := Subgroup.card_dvd_of_le (le_top : P₁ ≤ ⊤)
        rwa [Subgroup.card_top] at htop
      obtain ⟨j, hj, hdj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3k
      rw [hdj]
      have h9 : 3 ^ j ≤ 6 := Nat.le_of_dvd (by norm_num) (hdj ▸ h6)
      have hj1 : j ≤ 1 := by
        by_contra hcon
        have h2 : 2 ≤ j := by omega
        have hle : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h2
        norm_num at hle
        omega
      interval_cases j
      · norm_num
      · norm_num
    have hres_mem : ∀ (i : Fin 3) (x : P₁),
        resAt i x ∈ Subgroup.zpowers (resAt i z₁) := by
      intro i x
      exact w16g_mem_zpowers_of_card_le_six (hAutLe i) (hzres i) (hresOrd i x)
    let gz : ↥(Subgroup.zpowers z) := ⟨z, Subgroup.mem_zpowers z⟩
    have hzgen : ∀ a : ↥(Subgroup.zpowers z), a ∈ Subgroup.zpowers gz := by
      intro a
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)⟩
    have hgzord : orderOf gz = 3 := by
      have h := Subgroup.orderOf_coe gz
      rw [show (gz : MulAut W) = z from rfl, hz3] at h
      exact h.symm
    have hzpCard : Nat.card ↥(Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, hz3]
    let eZ : Multiplicative (ZMod 3) ≃* ↥(Subgroup.zpowers z) :=
      zmodMulEquivOfGenerator hzgen hzpCard

    let θ : ∀ i, ↥(Subgroup.zpowers z) →* MulAut ↥(U i) := fun i =>
      (resHom (U i)).comp (Subgroup.inclusion (hzpStab i))
    have hθz : ∀ i, θ i gz = resAt i z₁ := by
      intro i
      apply MulEquiv.ext
      intro u
      exact Subtype.ext rfl
    have hθord : ∀ i, orderOf (θ i gz) = 3 := by
      intro i
      rw [hθz i]
      exact hzres i
    have hθinj : ∀ i, Function.Injective (θ i) := by
      intro i a b hab
      have h1 : θ i (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hzgen (a * b⁻¹))
      have h2 : (θ i gz) ^ m = 1 := by rw [← map_zpow (θ i) gz m, hm, h1]
      have h3 : (3 : ℤ) ∣ m := by
        have h3' : (orderOf (θ i gz) : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr h2
        rwa [hθord i] at h3'
      have h4 : a * b⁻¹ = 1 := by
        rw [← hm]
        exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [hgzord]; exact h3)
      exact mul_inv_eq_one.mp h4
    have hex : ∀ (i : Fin 3) (x : P₁), ∃ a : ↥(Subgroup.zpowers z), θ i a = resAt i x := by
      intro i x
      have hmem : resAt i x ∈ Subgroup.zpowers (θ i gz) := by
        rw [hθz i]
        exact hres_mem i x
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact ⟨gz ^ m, by rw [map_zpow, hm]⟩
    let φ : ∀ i, P₁ →* Multiplicative (ZMod 3) := fun i =>
      { toFun := fun x => eZ.symm (Classical.choose (hex i x))
        map_one' := by
          have harg : Classical.choose (hex i 1) = 1 := by
            apply hθinj i
            rw [Classical.choose_spec (hex i 1)]
            simp
          rw [harg, map_one]
        map_mul' := by
          intro x y
          have harg : Classical.choose (hex i (x * y)) =
              Classical.choose (hex i x) * Classical.choose (hex i y) := by
            apply hθinj i
            rw [map_mul (θ i), Classical.choose_spec (hex i (x * y)), map_mul (resAt i),
              Classical.choose_spec (hex i x), Classical.choose_spec (hex i y)]
          rw [harg, map_mul eZ.symm] }
    let a : Fin 3 → P₁ → ↥(Subgroup.zpowers z) := fun i x => eZ (φ i x)
    have hφ_spec : ∀ (i : Fin 3) (x : P₁), θ i (a i x) = resAt i x := by
      intro i x
      show θ i (eZ (eZ.symm (Classical.choose (hex i x)))) = resAt i x
      rw [MulEquiv.apply_symm_apply]
      exact Classical.choose_spec (hex i x)
    haveI hP₁norm : P₁.Normal := MonoidHom.normal_ker cH
    have hker_c : ∀ x : ↥P, x ∈ P₁ → c x = 0 := by
      intro x hx
      have h := MonoidHom.mem_ker.mp hx
      rw [show cH x = Multiplicative.ofAdd (c x) from rfl] at h
      exact Multiplicative.ofAdd.injective h
    have hact : ∀ (i : Fin 3) (x : P₁) (v : ↥(U i)),
        ((resAt i x) v : W) = (a i x : MulAut W) (v : W) := by
      intro i x v
      have h := hφ_spec i x
      calc ((resAt i x) v : W) = ((θ i (a i x)) v : W) := by rw [h]
        _ = (a i x : MulAut W) (v : W) := rfl
    have hsurj : ∀ (g : MulAut W) (i j : Fin 3), (∀ u ∈ U i, g u ∈ U j) →
        ∀ u ∈ U j, ∃ v ∈ U i, g v = u := by
      intro g i j hmap u hu
      have hsub : (U i).map g.toMonoidHom ≤ U j := by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
        exact hmap v hv
      have heq : (U i).map g.toMonoidHom = U j := by
        refine Subgroup.eq_of_le_of_card_ge hsub ?_
        rw [Subgroup.card_map_of_injective (K := U i) g.injective, hUcard i, hUcard j]
      rw [← heq] at hu
      obtain ⟨v, hv, hv'⟩ := Subgroup.mem_map.mp hu
      exact ⟨v, hv, hv'⟩
    have hgcomm : ∀ g : ↥P, ∀ a : ↥(Subgroup.zpowers z),
        (g : MulAut W) * (a : MulAut W) = (a : MulAut W) * g := by
      intro g a
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      rw [← hm]
      have hc : Commute (g : MulAut W) z := hzc g g.2
      exact (hc.zpow_right m).eq
    have htcomm : ∀ a : ↥(Subgroup.zpowers z),
        t * (a : MulAut W) = (a : MulAut W) * t := by
      intro a
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      rw [← hm]
      have hc : Commute t z := by
        rw [Commute]
        calc t * z = (t * z * t⁻¹) * t := by group
          _ = z * t := by rw [hzt]
      exact (hc.zpow_right m).eq
    let s : P₁ →* Multiplicative (ZMod 3) := ∏ i : Fin 3, φ i
    have hs_apply : ∀ x : P₁, s x = φ 0 x * φ 1 x * φ 2 x := by
      intro x
      have h : s x = ∏ i : Fin 3, φ i x := rfl
      rw [h, Fin.prod_univ_three]
    have hcoord_g : ∀ (g : ↥P) (n : P₁) (i : Fin 3),
        φ (i + c g) ⟨g * (n : ↥P) * g⁻¹, hP₁norm.conj_mem (n : ↥P) n.2 g⟩ = φ i n := by
      intro g n i
      have hkey : resAt (i + c g) ⟨g * (n : ↥P) * g⁻¹, hP₁norm.conj_mem _ n.2 g⟩ =
          θ (i + c g) (a i n) := by
        apply MulEquiv.ext
        intro u
        obtain ⟨v, hv, htv⟩ := hsurj (g : MulAut W) i (i + c g) (fun w hw => hc_spec g i w hw) u u.2
        apply Subtype.ext
        have hnv : (((n : ↥P) : MulAut W)) v = (a i n : MulAut W) v := hact i n ⟨v, hv⟩
        calc (((resAt (i + c g) ⟨g * (n : ↥P) * g⁻¹, hP₁norm.conj_mem _ n.2 g⟩) u :
            ↥(U (i + c g))) : W)
            = (g : MulAut W) (((n : ↥P) : MulAut W) ((g : MulAut W)⁻¹ u)) := rfl
          _ = (g : MulAut W) (((n : ↥P) : MulAut W) v) := by
              rw [show (g : MulAut W)⁻¹ u = v from by
                rw [← htv]; exact MulEquiv.symm_apply_apply (g : MulAut W) v]
          _ = (g : MulAut W) ((a i n : MulAut W) v) := by rw [hnv]
          _ = ((g : MulAut W) * (a i n : MulAut W)) v := rfl
          _ = ((a i n : MulAut W) * (g : MulAut W)) v := by rw [hgcomm g (a i n)]
          _ = (a i n : MulAut W) ((g : MulAut W) v) := rfl
          _ = (a i n : MulAut W) u := by rw [htv]
          _ = ((θ (i + c g) (a i n)) u : W) := rfl
      have h1 : a (i + c g) ⟨g * (n : ↥P) * g⁻¹, hP₁norm.conj_mem _ n.2 g⟩ =
          a i n := by
        apply hθinj (i + c g)
        rw [hφ_spec (i + c g) ⟨g * (n : ↥P) * g⁻¹, hP₁norm.conj_mem _ n.2 g⟩, hkey]
      exact eZ.injective h1
    have hinv : ∀ (g : ↥P) (n : P₁),
        s ⟨g * (n : ↥P) * g⁻¹, hP₁norm.conj_mem (n : ↥P) n.2 g⟩ = s n := by
      intro g n
      have hprod : (∏ i : Fin 3, φ i ⟨g * (n : ↥P) * g⁻¹,
          hP₁norm.conj_mem (n : ↥P) n.2 g⟩) = ∏ i : Fin 3, φ i n := by
        rw [show (∏ i : Fin 3, φ i ⟨g * (n : ↥P) * g⁻¹,
            hP₁norm.conj_mem (n : ↥P) n.2 g⟩) =
          ∏ i : Fin 3, φ (i + c g) ⟨g * (n : ↥P) * g⁻¹,
            hP₁norm.conj_mem (n : ↥P) n.2 g⟩ from
          (w16g_prod_fin_three_add (fun j => φ j ⟨g * (n : ↥P) * g⁻¹,
            hP₁norm.conj_mem (n : ↥P) n.2 g⟩) (c g)).symm]
        exact Finset.prod_congr rfl (fun i _ => hcoord_g g n i)
      rw [show s ⟨g * (n : ↥P) * g⁻¹, hP₁norm.conj_mem (n : ↥P) n.2 g⟩ =
          ∏ i : Fin 3, φ i ⟨g * (n : ↥P) * g⁻¹, hP₁norm.conj_mem (n : ↥P) n.2 g⟩ from rfl,
        hprod]
      rfl
    obtain ⟨y, hyP, hy1⟩ := hy
    let yP : ↥P := ⟨y, hyP⟩
    have hcyP : c yP = 1 :=
      w16g_shift_unique hind hrk (d := c yP) (e := 1) (hc_spec yP) hy1
    have hyPnot : yP ∉ P₁ := by
      intro hmem
      have h := hker_c yP hmem
      rw [hcyP] at h
      exact one_ne_zero h
    have htopM : Subgroup.zpowers (cH yP) = ⊤ := by
      have h3 : (cH yP) ^ 3 = 1 := by
        rw [show cH yP = Multiplicative.ofAdd (c yP) from rfl, hcyP]
        decide
      have hne : cH yP ≠ 1 := by
        intro h
        exact hyPnot (by rw [MonoidHom.mem_ker]; exact h)
      have hord : orderOf (cH yP) = 3 := orderOf_eq_prime h3 hne
      refine Subgroup.eq_of_le_of_card_ge le_top ?_
      rw [Nat.card_zpowers, hord]
      simp [Nat.card_zmod]
    have hTop : P₁ ⊔ Subgroup.zpowers yP = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have himg : cH g ∈ Subgroup.zpowers (cH yP) := by
        rw [htopM]; exact Subgroup.mem_top _
      have hmap : (Subgroup.zpowers yP).map cH = Subgroup.zpowers (cH yP) :=
        MonoidHom.map_zpowers cH yP
      rw [← hmap] at himg
      obtain ⟨h, hh, hhe⟩ := Subgroup.mem_map.mp himg
      have hmem : g * h⁻¹ ∈ P₁ := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hhe]
        exact mul_inv_cancel _
      have hg : g = (g * h⁻¹) * h := by group
      rw [hg]
      exact Subgroup.mul_mem_sup hmem hh
    have hsplit : ∀ g : ↥P, ∃ n : P₁, ∃ i : ℤ, g = (n : ↥P) * yP ^ i := by
      intro g
      have hg : g ∈ P₁ ⊔ Subgroup.zpowers yP := by rw [hTop]; exact Subgroup.mem_top g
      obtain ⟨n, hn, z, hz, hnz⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact ⟨⟨n, hn⟩, i, by rw [← hnz, hi]⟩
    obtain ⟨σ, hσ⟩ := SmD6Grp.exists_conj_hom (G := MulAut W) t h.hn
    obtain ⟨σ₀, hσ₀⟩ := htU
    have htt : t * t = 1 := by rw [← pow_two, ← h.ht]; exact pow_orderOf_eq_one t
    have hττ : ∀ x : ↥P, σ (σ x) = x := by
      intro x
      apply Subtype.ext
      rw [hσ, hσ]
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
      rw [htinv]
      calc t * (t * (x : MulAut W) * t) * t = (t * t) * (x : MulAut W) * (t * t) := by group
        _ = x := by rw [htt]; group
    have hτN : ∀ n : P₁, σ (n : ↥P) ∈ P₁ := by
      intro n
      rw [MonoidHom.mem_ker]
      have hcn : c (n : ↥P) = 0 := hker_c (n : ↥P) n.2
      have hshift : c (σ (n : ↥P)) = 0 := by
        refine w16g_shift_unique hind hrk (d := c (σ (n : ↥P))) (e := 0)
          (hc_spec (σ (n : ↥P))) ?_
        intro i u hu
        obtain ⟨v, hv, htv⟩ := hsurj t (σ₀.symm i) i (by
          intro w hw
          have h := hσ₀ (σ₀.symm i) w hw
          rwa [Equiv.apply_symm_apply] at h) u hu
        have hnv : ((n : ↥P) : MulAut W) v ∈ U (σ₀.symm i) := by
          have h := hc_spec (n : ↥P) (σ₀.symm i) v hv
          rw [hcn, add_zero] at h
          exact h
        have h1 : (((σ (n : ↥P) : ↥P)) : MulAut W) u = t (((n : ↥P) : MulAut W) (t⁻¹ u)) := by
          rw [hσ]
          rfl
        rw [h1, show t⁻¹ u = v from by
          rw [← htv]; exact MulEquiv.symm_apply_apply t v]
        have h := hσ₀ (σ₀.symm i) (((n : ↥P) : MulAut W) v) hnv
        rw [Equiv.apply_symm_apply] at h
        simpa using h
      show Multiplicative.ofAdd (c (σ (n : ↥P))) = 1
      rw [hshift]
      rfl
    have hcoord_t : ∀ (n : P₁) (i : Fin 3),
        φ (σ₀ i) ⟨σ (n : ↥P), hτN n⟩ = φ i n := by
      intro n i
      have hkey : resAt (σ₀ i) ⟨σ (n : ↥P), hτN n⟩ = θ (σ₀ i) (a i n) := by
        apply MulEquiv.ext
        intro u
        obtain ⟨v, hv, htv⟩ := hsurj t i (σ₀ i) (fun w hw => hσ₀ i w hw) u u.2
        apply Subtype.ext
        have hnv : (((n : ↥P) : MulAut W)) v = (a i n : MulAut W) v := hact i n ⟨v, hv⟩
        have hval : (((⟨σ (n : ↥P), hτN n⟩ : P₁) : ↥P) : MulAut W) = t * (n : ↥P) * t⁻¹ := by
          show ((σ (n : ↥P) : ↥P) : MulAut W) = t * (n : ↥P) * t⁻¹
          rw [hσ]
        calc (((resAt (σ₀ i) ⟨σ (n : ↥P), hτN n⟩) u : ↥(U (σ₀ i))) : W)
            = (((⟨σ (n : ↥P), hτN n⟩ : P₁) : ↥P) : MulAut W) u := rfl
          _ = (t * (n : ↥P) * t⁻¹) u := by rw [hval]
          _ = t (((n : ↥P) : MulAut W) (t⁻¹ u)) := rfl
          _ = t (((n : ↥P) : MulAut W) v) := by
              rw [show t⁻¹ u = v from by rw [← htv]; exact MulEquiv.symm_apply_apply t v]
          _ = t ((a i n : MulAut W) v) := by rw [hnv]
          _ = (t * (a i n : MulAut W)) v := rfl
          _ = ((a i n : MulAut W) * t) v := by rw [htcomm (a i n)]
          _ = (a i n : MulAut W) (t v) := rfl
          _ = (a i n : MulAut W) u := by rw [htv]
          _ = ((θ (σ₀ i) (a i n)) u : W) := rfl
      have h1 : a (σ₀ i) ⟨σ (n : ↥P), hτN n⟩ = a i n := by
        apply hθinj (σ₀ i)
        rw [hφ_spec (σ₀ i) ⟨σ (n : ↥P), hτN n⟩, hkey]
      exact eZ.injective h1
    have hτs : ∀ n : P₁, s ⟨σ (n : ↥P), hτN n⟩ = s n := by
      intro n
      have hprod : (∏ i : Fin 3, φ i ⟨σ (n : ↥P), hτN n⟩) = ∏ i : Fin 3, φ i n := by
        rw [← Equiv.prod_comp σ₀ (fun j => φ j ⟨σ (n : ↥P), hτN n⟩)]
        exact Finset.prod_congr rfl (fun i _ => hcoord_t n i)
      rw [show s ⟨σ (n : ↥P), hτN n⟩ = ∏ i : Fin 3, φ i ⟨σ (n : ↥P), hτN n⟩ from rfl, hprod]
      rfl
    have hgen : ∀ g : ↥P, g ∈ Subgroup.closure {x : ↥P | ∃ h : ↥P, x = h * (σ h)⁻¹} := by
      have hmem : ∀ a : ↥P, (a : MulAut W) * t * (a : MulAut W)⁻¹ * t⁻¹ ∈ P := by
        intro a
        have h1 : t * (a : MulAut W)⁻¹ * t⁻¹ ∈ P := h.hn a⁻¹ (P.inv_mem a.2)
        have h2 : (a : MulAut W) * (t * (a : MulAut W)⁻¹ * t⁻¹) ∈ P := P.mul_mem a.2 h1
        simpa [mul_assoc] using h2
      have hle : ⁅P, Subgroup.zpowers t⁆ ≤
          (Subgroup.closure {x : ↥P | ∃ h : ↥P, x = h * (σ h)⁻¹}).map P.subtype := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rcases w16g_zpowers_eq_one_or_self htt hb with hb1 | hbt
        · rw [hb1]; simp
        · rw [hbt]
          refine Subgroup.mem_map.mpr ⟨⟨_, hmem ⟨a, ha⟩⟩, ?_, rfl⟩
          apply Subgroup.subset_closure
          refine ⟨⟨a, ha⟩, ?_⟩
          apply Subtype.ext
          show (a : MulAut W) * t * (a : MulAut W)⁻¹ * t⁻¹ =
            (a : MulAut W) * (σ ⟨a, ha⟩ : MulAut W)⁻¹
          rw [hσ ⟨a, ha⟩]
          group
      intro g
      have hg' : (g : MulAut W) ∈ (Subgroup.closure
          {x : ↥P | ∃ h : ↥P, x = h * (σ h)⁻¹}).map P.subtype := (h.hc ▸ hle) g.2
      obtain ⟨h', hh', hh'eq⟩ := Subgroup.mem_map.mp hg'
      rwa [← Subtype.ext hh'eq]
    have hs1 : ∀ n : P₁, s n = 1 := by
      have h2 : ∀ a : Multiplicative (ZMod 3), a * a = 1 → a = 1 := by
        intro a ha
        have hx : a.toAdd + a.toAdd = 0 := by
          have h := congrArg Multiplicative.toAdd ha
          simpa using h
        have h2' : (2 : ZMod 3) * a.toAdd = 0 := by
          rw [two_mul]; exact hx
        have hne : (2 : ZMod 3) ≠ 0 := by decide
        have hzero := (mul_eq_zero.mp h2').resolve_left hne
        exact Multiplicative.toAdd.injective (by simpa using hzero)
      exact w16g_hom_eq_one_of_generated (N := P₁) s h2 hττ hτN hτs hinv hsplit hgen
    have hinj : Function.Injective (fun x : P₁ => (φ 0 x, φ 1 x)) := by
      intro x y hxy
      have h0 : φ 0 x = φ 0 y := congrArg Prod.fst hxy
      have h1 : φ 1 x = φ 1 y := congrArg Prod.snd hxy
      have h2 : φ 2 x = φ 2 y := by
        have hx := hs1 x
        have hy := hs1 y
        rw [hs_apply x] at hx
        rw [hs_apply y] at hy
        have h : φ 0 x * φ 1 x * φ 2 x = φ 0 y * φ 1 y * φ 2 y := by rw [hx, hy]
        rw [h0, h1] at h
        exact mul_left_cancel h
      have hall : ∀ i : Fin 3, φ i x = φ i y := by
        intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      have hres : ∀ i : Fin 3, resAt i x = resAt i y := by
        intro i
        have hall_a : a i x = a i y := congrArg eZ (hall i)
        exact (hφ_spec i x).symm.trans ((congrArg (θ i) hall_a).trans (hφ_spec i y))
      have hact_eq : ∀ (i : Fin 3) (u : W), u ∈ U i →
          (x : MulAut W) u = (y : MulAut W) u := by
        intro i u hu
        have h1 := hact i x ⟨u, hu⟩
        have h2 := hact i y ⟨u, hu⟩
        have h3 : (x : MulAut W) u = ((resAt i x) ⟨u, hu⟩ : W) := rfl
        have h4 : (y : MulAut W) u = ((resAt i y) ⟨u, hu⟩ : W) := rfl
        have hall_a : a i x = a i y := congrArg eZ (hall i)
        have h5 : (a i x : MulAut W) u = (a i y : MulAut W) u := by rw [hall_a]
        rw [h3, h1, h5, ← h2, ← h4]
      have hsup3 : (⨆ i : Fin 3, U i) = (U 0 ⊔ U 1) ⊔ U 2 := by
        apply le_antisymm
        · apply iSup_le
          intro i
          fin_cases i
          · exact le_trans le_sup_left le_sup_left
          · exact le_trans le_sup_right le_sup_left
          · exact le_sup_right
        · apply sup_le
          · exact sup_le (le_iSup U 0) (le_iSup U 1)
          · exact le_iSup U 2
      have hxy : ∀ u : W, (x : MulAut W) u = (y : MulAut W) u := by
        intro u
        have hu : u ∈ (⨆ i, U i) := by rw [hsup]; exact Subgroup.mem_top u
        rw [hsup3] at hu
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
        obtain ⟨a0, ha0, a1, ha1, rfl⟩ := Subgroup.mem_sup.mp ha
        calc (x : MulAut W) ((a0 * a1) * b)
            = ((x : MulAut W) a0 * (x : MulAut W) a1) * (x : MulAut W) b := by simp
          _ = ((y : MulAut W) a0 * (y : MulAut W) a1) * (y : MulAut W) b := by
              rw [hact_eq 0 a0 ha0, hact_eq 1 a1 ha1, hact_eq 2 b hb]
          _ = (y : MulAut W) ((a0 * a1) * b) := by simp
      exact Subtype.ext (Subtype.ext (MulEquiv.ext hxy))
    have hle := Nat.card_le_card_of_injective (fun x : P₁ => (φ 0 x, φ 1 x)) hinj
    rw [Nat.card_prod] at hle
    have hM : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp [Nat.card_zmod]
    rw [hM] at hle
    omega
  calc Nat.card P = Nat.card ↥P := rfl
    _ = Nat.card (↥P ⧸ P₁) * Nat.card P₁ := hcard_eq
    _ ≤ 3 * Nat.card P₁ := Nat.mul_le_mul_right _ hquot_le
    _ ≤ 3 * 9 := Nat.mul_le_mul_left _ hP₁_le
    _ = 27 := by norm_num

theorem w16h_central_extraspecial (h : Cfg132 t P)
    {z : MulAut W} (hzP : z ∈ P) (hz3 : orderOf z = 3) (hzc : ∀ y ∈ P, y * z = z * y)
    (hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → x ∈ Subgroup.zpowers z)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z)
    (hcard : Nat.card P ≤ 27) : IsPOnePlusTwo 3 ↥P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htt : t * t = 1 := by rw [← pow_two, ← h.ht]; exact pow_orderOf_eq_one t
  have hnc : ∃ u v : ↥P, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    have hcentral : ∀ x ∈ P, ∀ y ∈ P, y * x = x * y := fun x hx y hy =>
      congrArg Subtype.val (hcon ⟨y, hy⟩ ⟨x, hx⟩)
    have htfix : ∀ x ∈ P, t * x * t⁻¹ = x := fun x hx => hZ x hx (fun y hy => by
      have := hcentral x hx y hy
      exact this)
    have hbot : ⁅P, Subgroup.zpowers t⁆ = ⊥ := by
      apply le_antisymm _ bot_le
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot]
      rcases w16g_zpowers_eq_one_or_self htt hb with hb1 | hbt
      · rw [hb1]; simp
      · rw [hbt]
        rw [commutatorElement_eq_one_iff_mul_comm]
        have h1 := htfix a ha
        have h2 : t * a = a * t := by
          calc t * a = t * a * t⁻¹ * t := by group
            _ = a * t := by rw [h1]
        exact h2.symm
    have hPeq : P = ⊥ := by rw [← h.hc]; exact hbot
    exact h.hne hPeq
  have hcard27 : Nat.card ↥P = 27 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).mp h.hP
    have hk_le : k ≤ 3 := by
      have hle3 : 3 ^ k ≤ 3 ^ 3 := by rw [← hk]; simpa using hcard
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle3
    have hk_ge : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk0', pow_zero] at hk
      exact h.hne ((Subgroup.card_eq_one).mp hk)
    have hk_ne1 : k ≠ 1 := by
      intro h1
      have hcard3 : Nat.card ↥P = 3 := by rw [hk, h1]; norm_num
      haveI : IsCyclic ↥P := isCyclic_of_prime_card hcard3
      obtain ⟨u, v, huv⟩ := hnc
      exact huv ((IsMulCommutative.is_comm (M := ↥P)).comm u v)
    have hk_ne2 : k ≠ 2 := by
      intro h2
      have hcard9 : Nat.card ↥P = 3 ^ 2 := by rw [hk, h2]
      haveI : IsMulCommutative ↥P :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard9
      obtain ⟨u, v, huv⟩ := hnc
      exact huv ((IsMulCommutative.is_comm (M := ↥P)).comm u v)
    have hk3 : k = 3 := by omega
    rw [hk, hk3]; norm_num
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hcard27]; norm_num)
  haveI : IsMulCommutative (↥P ⧸ Subgroup.center ↥P) :=
    SmD6Grp.isMulCommutative_quotient_center hcard27 hnc
  have hQcomm : ∀ a b : ↥P ⧸ Subgroup.center ↥P, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := ↥P ⧸ Subgroup.center ↥P)).comm a b
  obtain ⟨σ, hσ, hσσ, hZfix, hinv⟩ := w16g_inverts_center_quotient htt h.hn h.hc hZ hQcomm
  have hexp : ∀ x : ↥P, x ^ 3 = 1 :=
    w16g_exp_three_of_inverts_center hcard27 hnc σ hσσ hZfix hinv
  exact ⟨isExtraspecial_three_of_card_27 hcard27 hnc hexp,
    by rw [hcard27]; norm_num, hexp⟩

theorem w16h_central (h : Cfg132 t P) (hind : NoDecomp132 t P)
    (hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z) :
    IsPOnePlusTwo 3 ↥P ∧ rk ↥(commSub ⊤ P) = 6 := by
  obtain ⟨z, hzP, hz3, hzc, hZP, hfix, hrk2⟩ := w16h_central_center h hind hZ
  have hzt : t * z * t⁻¹ = z := hZ z hzP hzc
  obtain ⟨U, hindU, hsup, hrkU, hzU, hPU, hyU, htU⟩ :=
    w16h_central_decomp h hZ hzP hz3 hzc hZP hfix hrk2
  have hcard :=
    w16h_central_card_le h hzP hz3 hzc hzt hfix hindU hsup hrkU hzU hPU hyU htU
  refine ⟨w16h_central_extraspecial h hzP hz3 hzc hZP hZ hcard, ?_⟩
  have hcommTop : commSub ⊤ P = ⊤ := by
    have hzle : Subgroup.zpowers z ≤ P := Subgroup.zpowers_le.mpr hzP
    haveI : Finite (Subgroup.zpowers z) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hz3]; norm_num)
    have hodd : Odd (Nat.card (Subgroup.zpowers z)) := by
      rw [Nat.card_zpowers, hz3]; norm_num
    have hfixbot : fixV (Subgroup.zpowers z) = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      exact hfix u ((mem_fixV.mp hu) z (Subgroup.mem_zpowers z))
    have hcommz : commSub ⊤ (Subgroup.zpowers z) = ⊤ := by
      have hcompl := isCompl_fixV_commV_of_odd (Subgroup.zpowers z) hodd h.hW
      have hcv : commV (Subgroup.zpowers z) = ⊤ := by
        simpa [hfixbot] using hcompl.2
      rwa [commV_eq_commSub] at hcv
    have hle : commSub ⊤ (Subgroup.zpowers z) ≤ commSub ⊤ P :=
      commSub_mono (le_refl (⊤ : Subgroup W)) hzle
    rw [hcommz] at hle
    exact eq_top_iff.mpr hle
  have hrkW : rk W = 6 := by
    have hprod : Nat.card W = ∏ i : Fin 3, Nat.card ↥(U i) := by
      have h := CFSG.Quasithin.A38c16.Blocks.card_iSup_of_iSupIndep U hindU
      rw [hsup] at h
      simpa using h
    have hUi : ∀ i : Fin 3, Nat.card ↥(U i) = 4 := by
      intro i
      rw [card_eq_two_pow h.hW (U i), hrkU i]
      norm_num
    have hcardW : Nat.card W = 64 := by
      rw [hprod]
      simp only [hUi]
      norm_num
    unfold rk
    rw [hcardW, show (64 : ℕ) = 2 ^ 6 by norm_num, padicValNat.prime_pow]
  rw [hcommTop, rk_top, hrkW]

end CFSG.LocalAnalysis.WeakClosure81
