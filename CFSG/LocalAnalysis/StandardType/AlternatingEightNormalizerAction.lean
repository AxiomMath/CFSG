module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.StandardType.AlternatingEightSylowThreeKlein

public section

namespace CFSG.StandardType

namespace AlternatingEightAction

variable {G : Type*} [Group G]

def centerQuotientPerm (J : Subgroup G)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8)) : ↥J →* Equiv.Perm (Fin 8) :=
  (alternatingGroup (Fin 8)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J)))

theorem mem_ker_centerQuotientPerm_iff (J : Subgroup G)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8)) (j : ↥J) :
    centerQuotientPerm J e j = 1 ↔ j ∈ Subgroup.center ↥J := by
  simp only [centerQuotientPerm, MonoidHom.comp_apply]
  have hsub : ∀ y : ↥(alternatingGroup (Fin 8)),
      (alternatingGroup (Fin 8)).subtype y = 1 ↔ y = 1 := by
    intro y
    constructor
    · intro h
      refine Subgroup.subtype_injective (alternatingGroup (Fin 8)) ?_
      rw [h, map_one]
    · intro h
      rw [h, map_one]
  rw [hsub]
  change e (QuotientGroup.mk' (Subgroup.center ↥J) j) = 1 ↔ j ∈ Subgroup.center ↥J
  rw [e.map_eq_one_iff]
  simpa using QuotientGroup.eq_one_iff (N := Subgroup.center ↥J) j

theorem mem_centralizer_of_inv_mul_conj_mem_center {J : Subgroup G} (hJ : commutator ↥J = ⊤)
    {b : G} (hb : b ∈ Subgroup.normalizer (J : Set G))
    (h : ∀ j j' : ↥J, (j' : G) = b * j * b⁻¹ → j⁻¹ * j' ∈ Subgroup.center ↥J) :
    b ∈ Subgroup.centralizer (J : Set G) := by
  haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ
  let φ : MulAut ↥J := Subgroup.normalizerMonoidHom J ⟨b, hb⟩
  have hcentral : ∀ j : ↥J, j⁻¹ * φ j ∈ Subgroup.center ↥J := by
    intro j
    refine h j (φ j) ?_
    rfl
  have hid : φ.toMonoidHom = MonoidHom.id ↥J :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
      φ.toMonoidHom hcentral
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : φ ⟨x, hx⟩ = ⟨x, hx⟩ :=
    congrArg (fun ψ : ↥J →* ↥J => ψ ⟨x, hx⟩) hid
  have hxval : b * x * b⁻¹ = x := congrArg Subtype.val hx'
  exact (mul_inv_eq_iff_eq_mul.mp hxval).symm

theorem exists_perm_hom_of_le_normalizer {J P : Subgroup G}
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8))
    (hP : P ≤ Subgroup.normalizer (J : Set G)) :
    ∃ π : ↥P →* Equiv.Perm (Fin 8), ∀ (b : ↥P) (j j' : ↥J),
      (j' : G) = (b : G) * j * (b : G)⁻¹ →
        centerQuotientPerm J e j' = π b * centerQuotientPerm J e j * (π b)⁻¹ := by
  classical
  let ψ : ↥P →* MulAut ↥J :=
    (Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hP)
  let cq : ↥P →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥J).comp ψ
  let ζ : ↥P →* MulAut (alternatingGroup (Fin 8)) :=
    (MulAut.congr e).toMonoidHom.comp cq
  let Φ : MulAut (alternatingGroup (Fin 8)) ≃* Equiv.Perm (Fin 8) :=
    (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
        (by norm_num) (by norm_num))).symm
  let π : ↥P →* Equiv.Perm (Fin 8) := Φ.toMonoidHom.comp ζ
  refine ⟨π, ?_⟩
  intro b j j' hj'
  have hψval : ∀ i : ↥J, ((ψ b) i : G) = (b : G) * (i : G) * (b : G)⁻¹ := by
    intro i
    rfl
  have hψj : ψ b j = j' := Subtype.ext ((hψval j).trans hj'.symm)
  have hζeq : ζ b = MulAut.conjNormal (π b) := by
    have h : MulAut.conjNormal (π b) = ζ b := by
      change Φ.symm (Φ (ζ b)) = ζ b
      rw [MulEquiv.symm_apply_apply]
    exact h.symm
  have hζapply : (ζ b) (e (QuotientGroup.mk' (Subgroup.center ↥J) j))
      = e (QuotientGroup.mk' (Subgroup.center ↥J) j') := by
    have h1 : (ζ b) (e (QuotientGroup.mk' (Subgroup.center ↥J) j))
        = e ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥J)
            (ψ b) (QuotientGroup.mk' (Subgroup.center ↥J) j)) := by
      show ((MulAut.congr e)
        ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥J) (ψ b)))
        (e (QuotientGroup.mk' (Subgroup.center ↥J) j)) = _
      simp [MulAut.congr_apply]
    rw [h1]
    change e ((CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient (ψ b))
      (QuotientGroup.mk' (Subgroup.center ↥J) j)) =
      e (QuotientGroup.mk' (Subgroup.center ↥J) j')
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk, hψj]
  have hconj : MulAut.conjNormal (π b) (e (QuotientGroup.mk' (Subgroup.center ↥J) j))
      = e (QuotientGroup.mk' (Subgroup.center ↥J) j') := by
    rw [← hζeq]
    exact hζapply
  change ((e (QuotientGroup.mk' (Subgroup.center ↥J) j') : alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8))
      = π b * ((e (QuotientGroup.mk' (Subgroup.center ↥J) j) : alternatingGroup (Fin 8)) :
          Equiv.Perm (Fin 8)) * (π b)⁻¹
  have hfinal := congrArg Subtype.val hconj
  rw [MulAut.conjNormal_apply] at hfinal
  exact hfinal.symm

theorem exists_two_subgroup_of_perm_hom {J P : Subgroup G}
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8))
    (hZ : IsPGroup 2 (Subgroup.center ↥J)) (hP : P ≤ Subgroup.normalizer (J : Set G))
    (π : ↥P →* Equiv.Perm (Fin 8))
    (hπ : ∀ (b : ↥P) (j j' : ↥J), (j' : G) = (b : G) * j * (b : G)⁻¹ →
      centerQuotientPerm J e j' = π b * centerQuotientPerm J e j * (π b)⁻¹)
    {V : Subgroup (Equiv.Perm (Fin 8))} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hVA : V ≤ alternatingGroup (Fin 8))
    (hVπ : π.range ≤ Subgroup.normalizer (V : Set (Equiv.Perm (Fin 8)))) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧ P ≤ Subgroup.normalizer (T : Set G) := by
  classical
  let q := centerQuotientPerm J e
  let T : Subgroup G := (V.comap q).map J.subtype
  have hker : q.ker = Subgroup.center ↥J := by
    ext j
    rw [MonoidHom.mem_ker, mem_ker_centerQuotientPerm_iff]
  have hqker : IsPGroup 2 q.ker := by
    rw [hker]
    exact hZ
  have hcomap : IsPGroup 2 (V.comap q) := hV2.comap_of_ker_isPGroup q hqker
  have hT2 : IsPGroup 2 T := hcomap.map J.subtype
  have hTJ : T ≤ J := by
    intro t ht
    obtain ⟨j, _, rfl⟩ := Subgroup.mem_map.mp ht
    exact j.2
  have hTne : T ≠ ⊥ := by
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
    have hvA : (v : Equiv.Perm (Fin 8)) ∈ alternatingGroup (Fin 8) := hVA v.2
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J)
      (e.symm ⟨(v : Equiv.Perm (Fin 8)), hvA⟩)
    have hqa : q a = (v : Equiv.Perm (Fin 8)) := by
      change ((e (QuotientGroup.mk' (Subgroup.center ↥J) a) : alternatingGroup (Fin 8)) :
        Equiv.Perm (Fin 8)) = (v : Equiv.Perm (Fin 8))
      rw [ha, MulEquiv.apply_symm_apply]
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨J.subtype a, Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩⟩, ?_⟩
    · rw [Subgroup.mem_comap]
      rw [hqa]
      exact v.2
    · intro h
      have ha1 : a = 1 := Subtype.ext (by simpa using congrArg Subtype.val h)
      have : (v : Equiv.Perm (Fin 8)) = 1 := by
        rw [← hqa, ha1, map_one]
      exact hv1 (Subtype.ext this)
  have hconjmem : ∀ (c : ↥P) (j : ↥J), q j ∈ V →
      q ⟨(c : G) * (j : G) * (c : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hP c.2) (j : G)).mp j.2⟩ ∈ V := by
    intro c j hj
    have h' := hπ c j ⟨(c : G) * (j : G) * (c : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hP c.2) (j : G)).mp j.2⟩ rfl
    rw [h']
    exact (Subgroup.mem_normalizer_iff.mp (hVπ ⟨c, rfl⟩) (q j)).mp hj
  have hforward : ∀ (c : ↥P) (t : G), t ∈ T → (c : G) * t * (c : G)⁻¹ ∈ T := by
    intro c t ht
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp ht
    rw [Subgroup.mem_comap] at hj
    exact Subgroup.mem_map.mpr ⟨⟨(c : G) * (j : G) * (c : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hP c.2) (j : G)).mp j.2⟩,
      by rw [Subgroup.mem_comap]; exact hconjmem c j hj, rfl⟩
  refine ⟨T, hTne, hT2, hTJ, ?_⟩
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact hforward ⟨b, hb⟩ t ht
  · intro ht
    have h := hforward ⟨b, hb⟩⁻¹ ((b : G) * t * (b : G)⁻¹) ht
    have hinv : ((⟨b, hb⟩⁻¹ : ↥P) : G) = (b : G)⁻¹ := by simp
    rw [hinv] at h
    simp only [inv_inv] at h
    have h' : (b : G)⁻¹ * ((b : G) * t * (b : G)⁻¹) * (b : G) = t := by group
    rwa [h'] at h

theorem exists_perm_hom_with_card_ker_le [Finite G] {J P : Subgroup G} (hJ : commutator ↥J = ⊤)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8))
    (hP : P ≤ Subgroup.normalizer (J : Set G)) :
    ∃ π : ↥P →* Equiv.Perm (Fin 8),
      (∀ (b : ↥P) (j j' : ↥J), (j' : G) = (b : G) * j * (b : G)⁻¹ →
        centerQuotientPerm J e j' = π b * centerQuotientPerm J e j * (π b)⁻¹) ∧
      Nat.card π.ker ≤ Nat.card ↥(P ⊓ Subgroup.centralizer (J : Set G)) := by
  classical
  obtain ⟨π, hπ⟩ := exists_perm_hom_of_le_normalizer e hP
  refine ⟨π, hπ, ?_⟩
  have hker : ∀ b : ↥P, π b = 1 → (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b hb
    refine mem_centralizer_of_inv_mul_conj_mem_center hJ (hP b.2) ?_
    intro j j' hj'
    have h1 := hπ b j j' hj'
    rw [hb] at h1
    have h2 : centerQuotientPerm J e j' = centerQuotientPerm J e j := by simpa using h1
    rw [← mem_ker_centerQuotientPerm_iff J e, map_mul, map_inv, h2, inv_mul_cancel]
  have hle : π.ker.map P.subtype ≤ P ⊓ Subgroup.centralizer (J : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b.2, hker b hb⟩
  calc Nat.card π.ker = Nat.card (π.ker.map P.subtype) :=
        (Subgroup.card_map_of_injective P.subtype_injective).symm
    _ ≤ Nat.card ↥(P ⊓ Subgroup.centralizer (J : Set G)) := Subgroup.card_le_of_le hle

theorem card_le_nine_mul_card_inf [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup G} (hJ : commutator ↥J = ⊤)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8))
    (hP : P ≤ Subgroup.normalizer (J : Set G)) (hPp : IsPGroup p P) :
    Nat.card P ≤ 9 * Nat.card ↥(P ⊓ Subgroup.centralizer (J : Set G)) := by
  obtain ⟨π, -, hker⟩ := exists_perm_hom_with_card_ker_le hJ e hP
  have hrp : IsPGroup p π.range := hPp.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  have h9 := AlternatingEightSylow.card_le_nine_of_isPGroup hp hp2 hrp
  rw [← Subgroup.card_ker_mul_card_range π, mul_comm 9]
  exact Nat.mul_le_mul hker h9

theorem prime_eq_three_of_large_action [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J P : Subgroup G} (hJ : commutator ↥J = ⊤)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8))
    (hP : P ≤ Subgroup.normalizer (J : Set G)) (hPp : IsPGroup p P)
    (hP4 : p ^ 4 ≤ Nat.card P)
    (hC : Nat.card ↥(P ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 2) :
    p = 3 := by
  have h9 := card_le_nine_mul_card_inf hp hp2 hJ e hP hPp
  have hPle : Nat.card P ≤ 9 * p ^ 2 := h9.trans (Nat.mul_le_mul_left 9 hC)
  have hp4 : p ^ 4 ≤ 9 * p ^ 2 := hP4.trans hPle
  have hsq : p ^ 2 ≤ 9 := by
    have hmul : p ^ 2 * p ^ 2 ≤ 9 * p ^ 2 := by
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ 9 * p ^ 2 := hp4
    exact Nat.le_of_mul_le_mul_right hmul (pow_pos hp.pos 2)
  have hpLe : p ≤ 3 := by
    refine (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp ?_
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    exact hsq
  have hpGe : 3 ≤ p := hp.odd_iff.mp (hp.odd_of_ne_two hp2)
  omega

theorem exists_two_subgroup_normalized_of_alternating_eight_quotient [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {J P : Subgroup G} (hJ : commutator ↥J = ⊤)
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8))
    (hZ : IsPGroup 2 (Subgroup.center ↥J)) (hP : P ≤ Subgroup.normalizer (J : Set G))
    (hPp : IsPGroup p P) (hP4 : p ^ 4 ≤ Nat.card P)
    (hC : Nat.card ↥(P ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 2) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧ P ≤ Subgroup.normalizer (T : Set G) := by
  classical
  obtain ⟨π, hπ, hkerle'⟩ := exists_perm_hom_with_card_ker_le hJ e hP
  have hkerle : Nat.card π.ker ≤ p ^ 2 := hkerle'.trans hC
  have hcard : Nat.card π.ker * Nat.card π.range = Nat.card P := Subgroup.card_ker_mul_card_range π
  have hrange : p ^ 2 ≤ Nat.card π.range := by
    have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
    by_contra hlt
    have hlt : Nat.card π.range < p ^ 2 := not_le.mp hlt
    have : Nat.card π.ker * Nat.card π.range < p ^ 2 * p ^ 2 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hkerle) (Nat.mul_lt_mul_of_pos_left hlt hpos)
    have h44 : p ^ 2 * p ^ 2 = p ^ 4 := by ring
    omega
  have hrp : IsPGroup p π.range := hPp.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  obtain ⟨V, hV0, hV2, hVA, hVn⟩ :=
    AlternatingEightSylow.exists_two_subgroup_normalized_of_isPGroup hp hp2 hrp hrange
  exact exists_two_subgroup_of_perm_hom e hZ hP π hπ hV0 hV2 hVA hVn

end AlternatingEightAction

end CFSG.StandardType
