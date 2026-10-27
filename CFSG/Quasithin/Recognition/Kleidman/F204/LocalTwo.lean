module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalA5
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Frame

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin
  CFSG.Quasithin.FA5 CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_three_conj_mem_borel (F : Frame L1 L2 S D X) {l : G} (hl : l ∈ L2)
    (hlB : l ∉ borelOf L2 S) :
    ∃ t ∈ borelOf L2 S, t ≠ 1 ∧ t ^ 3 = 1 ∧ l⁻¹ * t * l ∈ borelOf L2 S := by
  obtain ⟨e⟩ := F.pair.alt2
  have hsyl : IsSylowTwoOf (S ⊓ L2) L2 := F.pair.hyp.hyp.h2.sylow
  obtain ⟨hp, hodd, hmap⟩ := F1.map_borelOf_eq_normalizer hsyl
  set π : ↥L2 →* oTwoQuot ↥L2 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L2) with hπ
  set T : Subgroup ↥L2 := (S ⊓ L2).subgroupOf L2 with hT
  set Tb : Subgroup (oTwoQuot ↥L2) := T.map π with hTb
  set B2 : Subgroup ↥L2 := (borelOf L2 S).subgroupOf L2 with hB2
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ B2 := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe x).mp hx
    exact F1.sylow_le_borelOf L2 S (isSylowTwoOf_pCoreOf_le hsyl h1)
  have hT' : IsPGroup 2 (Tb.map e.toMonoidHom) := hp.map e.toMonoidHom
  have hodd' : ¬ 2 ∣ (Tb.map e.toMonoidHom).index := by
    rw [show e.toMonoidHom = (e : oTwoQuot ↥L2 →* Alt5) from rfl, Subgroup.index_map_equiv]
    exact hodd
  have hcard4 : Nat.card (Tb.map e.toMonoidHom) = 4 := card_eq_four_of_sylow hT' hodd'
  have hNmap : Subgroup.normalizer ((Tb.map e.toMonoidHom : Subgroup Alt5) : Set Alt5) =
      (Subgroup.normalizer (Tb : Set (oTwoQuot ↥L2))).map e.toMonoidHom :=
    (Subgroup.map_normalizer_eq_of_bijective Tb e.bijective).symm
  have hNmem : ∀ z : oTwoQuot ↥L2, z ∈ Subgroup.normalizer (Tb : Set (oTwoQuot ↥L2)) ↔
      e z ∈ Subgroup.normalizer ((Tb.map e.toMonoidHom : Subgroup Alt5) : Set Alt5) := by
    intro z
    rw [hNmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  set l' : ↥L2 := ⟨l, hl⟩ with hl'
  have hxN : e (π l') ∉ Subgroup.normalizer ((Tb.map e.toMonoidHom : Subgroup Alt5) : Set Alt5) := by
    intro h
    rw [← hNmem, ← hmap] at h
    obtain ⟨b, hb, hbl⟩ := h
    have hkl : b⁻¹ * l' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbl, inv_mul_cancel]
    have : l' ∈ B2 := by
      have h1 : b⁻¹ * l' ∈ B2 := hker hkl
      have := B2.mul_mem hb h1
      simpa using this
    exact hlB this
  obtain ⟨y, hyN, hxyN, hy3, hy1⟩ := alt5_two_point hcard4 hxN
  set ye : oTwoQuot ↥L2 := e.symm y with hye
  have hyeN : ye ∈ Subgroup.normalizer (Tb : Set (oTwoQuot ↥L2)) := by
    rw [hNmem]; simpa [hye] using hyN
  have hxyeN : (π l')⁻¹ * ye * π l' ∈ Subgroup.normalizer (Tb : Set (oTwoQuot ↥L2)) := by
    rw [hNmem]
    simpa [hye, map_mul, map_inv] using hxyN
  rw [← hmap] at hyeN hxyeN
  obtain ⟨c, hc, hcy⟩ := hyeN
  have hc3 : c ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hcy]
    have : e (ye ^ 3) = 1 := by rw [map_pow, hye, MulEquiv.apply_symm_apply]; exact hy3
    exact (MulEquiv.map_eq_one_iff e).mp this
  have hc3' : ((c ^ 3 : ↥L2) : G) ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe _).mp (by
    rwa [hπ, QuotientGroup.ker_mk'] at hc3)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L2 ⟨(c ^ 3 : ↥L2), hc3'⟩
  have hk' : ((c : G) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set t : G := (c : G) ^ 2 ^ k with ht
  have hcB : (c : G) ∈ borelOf L2 S := hc
  have htB : t ∈ borelOf L2 S := (borelOf L2 S).pow_mem hcB _
  have ht3 : t ^ 3 = 1 := by
    rw [ht, ← pow_mul, mul_comm, pow_mul]
    exact hk'
  have htc : (⟨t, (L2.pow_mem c.2 _)⟩ : ↥L2) = c ^ 2 ^ k := Subtype.ext (by simp [ht])
  have hπt : π (c ^ 2 ^ k) = ye ^ 2 ^ k := by rw [map_pow, hcy]
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 : c ^ 2 ^ k = 1 := Subtype.ext (by simpa [ht] using h1)
    have h3 : ye ^ 2 ^ k = 1 := by rw [← hπt, h2, map_one]
    have h4 : y ^ 2 ^ k = 1 := by
      have := congrArg e h3
      rwa [map_pow, hye, MulEquiv.apply_symm_apply, map_one] at this
    have hcop : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨h4, hy3⟩
    rw [hcop, pow_one] at this
    exact hy1 this
  have hpow : ((π l')⁻¹ * ye * π l') ^ 2 ^ k ∈ (Subgroup.map π B2) :=
    (Subgroup.map π B2).pow_mem hxyeN _
  obtain ⟨b, hb, hbeq⟩ := hpow
  have hconj : π (l'⁻¹ * c ^ 2 ^ k * l') = ((π l')⁻¹ * ye * π l') ^ 2 ^ k := by
    have hcp := conj_pow (a := (π l')⁻¹) (b := ye) (i := 2 ^ k)
    simp only [inv_inv] at hcp
    rw [map_mul, map_mul, map_inv, hπt]
    exact hcp.symm
  have hkl : b⁻¹ * (l'⁻¹ * c ^ 2 ^ k * l') ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbeq, hconj, inv_mul_cancel]
  have hB2l : l'⁻¹ * c ^ 2 ^ k * l' ∈ B2 := by
    have h1 : b⁻¹ * (l'⁻¹ * c ^ 2 ^ k * l') ∈ B2 := hker hkl
    have := B2.mul_mem hb h1
    simpa using this
  refine ⟨t, htB, ht1, ht3, ?_⟩
  have : (l'⁻¹ * c ^ 2 ^ k * l' : ↥L2) = ⟨l⁻¹ * t * l, L2.mul_mem (L2.mul_mem (L2.inv_mem hl)
      (L2.pow_mem c.2 _)) hl⟩ := Subtype.ext (by simp [ht, hl'])
  rw [this] at hB2l
  exact hB2l

theorem exists_three_conj_mem_B (F : Frame L1 L2 S D X) {g : G} (hg : g ∈ P2 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) :
    ∃ t ∈ bigB L1 L2 S, t ≠ 1 ∧ t ^ 3 = 1 ∧ g⁻¹ * t * g ∈ bigB L1 L2 S := by
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes F.B_le_normalizer_L2).mp hg
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  have hlB : l ∉ borelOf L2 S := by
    intro h
    apply hgB
    exact (bigB L1 L2 S).mul_mem (hB2B h) hb
  obtain ⟨t, ht, ht1, ht3, htl⟩ := exists_three_conj_mem_borel F hl hlB
  refine ⟨t, hB2B ht, ht1, ht3, ?_⟩
  have : (l * b)⁻¹ * t * (l * b) = b⁻¹ * (l⁻¹ * t * l) * b := by group
  rw [this]
  exact (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hb) (hB2B htl)) hb

end CFSG.Quasithin.Kleidman.F204
