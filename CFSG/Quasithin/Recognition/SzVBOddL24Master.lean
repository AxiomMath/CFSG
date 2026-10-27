module

public import CFSG.Quasithin.Recognition.SzVBOddL24Three

public section


namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_commute {V : Subgroup G} {x : G} (hx : ∀ v ∈ V, x * v = v * x) :
    x ∈ Subgroup.normalizer (V : Set G) :=
  Subgroup.centralizer_le_normalizer (V : Set G)
    (Subgroup.mem_centralizer_iff.mpr fun v hv => (hx v hv).symm)

omit [Finite G] in
theorem commute_conj_of_normalizer {V : Subgroup G} {s t : G}
    (hs : s ∈ Subgroup.normalizer (V : Set G)) (ht : ∀ v ∈ V, t * v = v * t) :
    ∀ v ∈ V, (s * t * s⁻¹) * v = v * (s * t * s⁻¹) := by
  intro v hv
  have hw : s⁻¹ * v * s ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set G)).inv_mem hs) v).mp hv
    simpa using this
  calc s * t * s⁻¹ * v = s * (t * (s⁻¹ * v * s)) * s⁻¹ := by group
    _ = s * ((s⁻¹ * v * s) * t) * s⁻¹ := by rw [ht _ hw]
    _ = v * (s * t * s⁻¹) := by group

theorem mem_normalizer_L2_of_mem_normalizer_V (hRO : RankOneListedFacts.{0})
    (h : R1SettingLegacyBare K1 L2 S Zs) {p : G} (hpP : p ∈ K1 ⊔ S)
    (hpV : p ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G)) :
    p ∈ Subgroup.normalizer (L2 : Set G) := by
  obtain ⟨κ, hκ, σ, hσ, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes h.hyp.h1.normalizes).mp hpP
  have hσV := S_le_normalizer_conjClosure hRO h hσ
  have hκV : κ ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) := by
    have := (Subgroup.normalizer (conjClosure Zs L2 : Set G)).mul_mem hpV
      ((Subgroup.normalizer (conjClosure Zs L2 : Set G)).inv_mem hσV)
    simpa using this
  have hκB : κ ∈ borelOf K1 S := by
    rw [← inf_normalizer_eq_borelOf hRO h]
    exact Subgroup.mem_inf.mpr ⟨hκ, hκV⟩
  exact (Subgroup.normalizer (L2 : Set G)).mul_mem (h.hyp.h2.borel_le hκB)
    (h.hyp.h2.normalizes hσ)

omit [Finite G] in
theorem conj_eq_one_iff' {H : Type*} [Group H] (σ τ : H) : σ * τ * σ⁻¹ = 1 ↔ τ = 1 := by
  simp

omit [Finite G] in
theorem odd_orderOf_conj {H : Type*} [Group H] (σ τ : H) (hτ : Odd (orderOf τ)) :
    Odd (orderOf (σ * τ * σ⁻¹)) := by
  refine Odd.of_dvd_nat hτ (orderOf_dvd_of_pow_eq_one ?_)
  rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]

theorem exists_stab_conj {P S V : Subgroup G} (hF : L24Facts P S V) {t : ↥P}
    (htN : (t : G) ∈ Subgroup.normalizer (V : Set G))
    (ht1 : MulAction.toPermHom ↥P (ConjSet P V) t ≠ 1)
    (ht3 : (MulAction.toPermHom ↥P (ConjSet P V) t) ^ 3 = 1) (ν : ConjSet P V) :
    ∃ s : ↥P, (s : G) ∈ S ∧ (s * t * s⁻¹) • ν = ν := by
  have hω : t • ConjSet.base P V = ConjSet.base P V :=
    Subtype.ext (F7.conjSub_eq_of_mem_normalizer htN)
  obtain ⟨μ, hμω, hμ⟩ := perm_exists_fixed hF.card_five (ConjSet.base P V)
    (MulAction.toPermHom ↥P (ConjSet P V) t) ht1 (by rw [← pow_three']; exact ht3) hω
  by_cases hν : ν = ConjSet.base P V
  · refine ⟨1, S.one_mem, ?_⟩
    rw [hν, one_mul, inv_one, mul_one]
    exact hω
  · obtain ⟨s, hsS, hs⟩ := hF.S_transitive μ ν hμω hν
    refine ⟨s, hsS, ?_⟩
    have hμ' : t • μ = μ := hμ
    rw [mul_smul, mul_smul, ← hs, inv_smul_smul, hμ']

theorem exists_conj_centralizing {P S V : Subgroup G} (hF : L24Facts P S V) {t : ↥P}
    (htN : (t : G) ∈ Subgroup.normalizer (V : Set G))
    (htV : ∀ v ∈ V, (t : G) * v = v * t) (hodd : Odd (orderOf (t : G)))
    (ht1 : MulAction.toPermHom ↥P (ConjSet P V) t ≠ 1)
    (ht3 : (MulAction.toPermHom ↥P (ConjSet P V) t) ^ 3 = 1) (ν : ConjSet P V) :
    ∃ (a : G) (haP : a ∈ P), (∀ v ∈ V, a * v = v * a) ∧ Odd (orderOf a) ∧
      (⟨a, haP⟩ : ↥P) • ν = ν ∧ MulAction.toPermHom ↥P (ConjSet P V) ⟨a, haP⟩ ≠ 1 ∧
      (MulAction.toPermHom ↥P (ConjSet P V) ⟨a, haP⟩) ^ 3 = 1 := by
  obtain ⟨s, hsS, hs⟩ := exists_stab_conj hF htN ht1 ht3 ν
  have hsN : (s : G) ∈ Subgroup.normalizer (V : Set G) := hF.S_le_normalizer hsS
  refine ⟨(s : G) * t * (s : G)⁻¹, (s * t * s⁻¹ : ↥P).2, commute_conj_of_normalizer hsN htV,
    odd_orderOf_conj _ _ hodd, hs, ?_, ?_⟩
  · show MulAction.toPermHom ↥P (ConjSet P V) (s * t * s⁻¹) ≠ 1
    rw [map_mul, map_mul, map_inv]
    exact fun h1 => ht1 ((conj_eq_one_iff' _ _).mp h1)
  · show (MulAction.toPermHom ↥P (ConjSet P V) (s * t * s⁻¹)) ^ 3 = 1
    rw [map_mul, map_mul, map_inv, conj_pow, ht3, mul_one, mul_inv_cancel]

omit [Finite G] in
theorem perm_mul_ne_one {P S V : Subgroup G} (hF : L24Facts P S V) {e a : ↥P}
    (he : (e : G) ∈ S) (ha1 : MulAction.toPermHom ↥P (ConjSet P V) a ≠ 1)
    (ha3 : (MulAction.toPermHom ↥P (ConjSet P V) a) ^ 3 = 1) :
    MulAction.toPermHom ↥P (ConjSet P V) (e * a) ≠ 1 := by
  intro h1
  rw [map_mul] at h1
  obtain ⟨n, hn⟩ := hF.S_pGroup ⟨(e : G), he⟩
  have hen : e ^ 2 ^ n = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  have hρe : (MulAction.toPermHom ↥P (ConjSet P V) e) ^ 2 ^ n = 1 := by
    rw [← map_pow, hen, map_one]
  have hρa : MulAction.toPermHom ↥P (ConjSet P V) a =
      (MulAction.toPermHom ↥P (ConjSet P V) e)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hρa2 : (MulAction.toPermHom ↥P (ConjSet P V) a) ^ 2 ^ n = 1 := by
    rw [hρa, inv_pow, hρe, inv_one]
  apply ha1
  have hd3 : orderOf (MulAction.toPermHom ↥P (ConjSet P V) a) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one ha3
  have hd2 : orderOf (MulAction.toPermHom ↥P (ConjSet P V) a) ∣ 2 ^ n :=
    orderOf_dvd_of_pow_eq_one hρa2
  have hcop : Nat.Coprime (orderOf (MulAction.toPermHom ↥P (ConjSet P V) a)) (2 ^ n) :=
    Nat.Coprime.coprime_dvd_left hd3 (Nat.Coprime.pow_right n (by norm_num))
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hd2)

theorem perm_cube_of_normalizer_odd {P S V : Subgroup G} (hF : L24Facts P S V) {x : ↥P}
    (hx : (x : G) ∈ Subgroup.normalizer (V : Set G)) (hodd : Odd (orderOf (x : G))) :
    (MulAction.toPermHom ↥P (ConjSet P V) x) ^ 3 = 1 := by
  refine perm_cube_of_odd hF.card_five (ConjSet.base P V) _ ?_ ?_
  · exact Subtype.ext (F7.conjSub_eq_of_mem_normalizer hx)
  · rw [Subgroup.orderOf_coe] at hodd
    exact Odd.of_dvd_nat hodd (orderOf_map_dvd _ _)

theorem exists_master (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    (hL : IsL2Quot 2 (OTwoQuot K1)) {k l₁ l₂ : G} (hk : k ∈ K1 ⊔ S) (hl₁ : l₁ ∈ L2)
    (hl₂ : l₂ ∈ L2) :
    ∃ (t : G) (htP : t ∈ K1 ⊔ S), t ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) ∧
      MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) ⟨t, htP⟩ ≠ 1 ∧
      (MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) ⟨t, htP⟩) ^ 3 = 1 ∧
      (l₁ * k * l₂)⁻¹ * t * (l₁ * k * l₂) ∈ K1 ⊔ S := by
  obtain ⟨z, hK⟩ := kleinData_of_setting hRO h
  have hF := l24Facts_of_setting hRO h hL
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hR := F112J2.hyp111R_of_setting hRO h
  have hSP : S ≤ K1 ⊔ S := le_sup_right
  have hLV : L2 ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    le_sup_left.trans hyp.normalizes
  have hLT : L2 ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) ≤ S :=
    (inf_le_inf_right _ le_sup_left).trans (inf_centralizer_le_T hyp
      (F112J2.isNaturalS3_of_setting hRO h) (F112J2.relIndex_L2S hR h.s3))
  obtain ⟨t₀, ht₀B, ht₀odd, ht₀1, ht₀3⟩ := exists_order_three hRO h hL
  have ht₀N := borelOf_le_normalizer_conjClosure h ht₀B
  have ht₀V : ∀ v ∈ conjClosure Zs L2, (t₀ : G) * v = v * (t₀ : G) := fun v hv =>
    commute_klein_of_odd_order hK.elemAbelian hK.card_eq hK.z_mem hK.z_ne_one
      (hK.z_cent _ t₀.2) (F7.conjSub_eq_of_mem_normalizer ht₀N) ht₀odd hv
  obtain ⟨ν, hν⟩ : ∃ ν : ConjSet (K1 ⊔ S) (conjClosure Zs L2),
      ν.1 = conjSub k (conjClosure Zs L2) := ⟨ConjSet.mk _ _ ⟨k, hk⟩, rfl⟩
  obtain ⟨a, haP, haV, haodd, haν, ha1, ha3⟩ :=
    exists_conj_centralizing hF ht₀N ht₀V ht₀odd ht₀1 ht₀3 ν
  have haνval : conjSub a ν.1 = ν.1 := congrArg Subtype.val haν
  have hakV : ∀ v ∈ conjClosure Zs L2, a * (k * v * k⁻¹) = (k * v * k⁻¹) * a := fun v hv =>
    commute_klein_of_odd_order (hK.isElemAbelian_point ν) (hK.card_point ν)
      (hK.z_mem_point ν) hK.z_ne_one (hK.z_cent a haP) haνval haodd
      (by rw [hν]; exact mul_mem_conjSub hv)
  have hbV : ∀ v ∈ conjClosure Zs L2, (k⁻¹ * a * k) * v = v * (k⁻¹ * a * k) := by
    intro v hv
    calc k⁻¹ * a * k * v = k⁻¹ * (a * (k * v * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * v * k⁻¹) * a) * k := by rw [hakV v hv]
      _ = v * (k⁻¹ * a * k) := by group
  have hbP : k⁻¹ * a * k ∈ K1 ⊔ S :=
    (K1 ⊔ S).mul_mem ((K1 ⊔ S).mul_mem ((K1 ⊔ S).inv_mem hk) haP) hk
  have hbL : k⁻¹ * a * k ∈ Subgroup.normalizer (L2 : Set G) :=
    mem_normalizer_L2_of_mem_normalizer_V hRO h hbP (mem_normalizer_of_commute hbV)
  have hc₂ : l₂⁻¹ * (k⁻¹ * a * k) * l₂ * (k⁻¹ * a * k)⁻¹ ∈ S := by
    have := hLT (commutator_mem_inf_centralizer (L := L2) (V := conjClosure Zs L2)
      (L2.inv_mem hl₂) hbL hLV hbV)
    rwa [inv_inv] at this
  have haN : a ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) := mem_normalizer_of_commute haV
  have haL : a ∈ Subgroup.normalizer (L2 : Set G) :=
    mem_normalizer_L2_of_mem_normalizer_V hRO h haP haN
  have he : l₁ * a * l₁⁻¹ * a⁻¹ ∈ S :=
    hLT (commutator_mem_inf_centralizer (L := L2) (V := conjClosure Zs L2) hl₁ haL hLV haV)
  have heq : l₁ * a * l₁⁻¹ = (l₁ * a * l₁⁻¹ * a⁻¹) * a := by group
  have htP : l₁ * a * l₁⁻¹ ∈ K1 ⊔ S := by
    rw [heq]
    exact (K1 ⊔ S).mul_mem (hSP he) haP
  have htN : l₁ * a * l₁⁻¹ ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem (hLV hl₁) haN)
      ((Subgroup.normalizer _).inv_mem (hLV hl₁))
  refine ⟨l₁ * a * l₁⁻¹, htP, htN, ?_, ?_, ?_⟩
  · have e : (⟨l₁ * a * l₁⁻¹, htP⟩ : ↥(K1 ⊔ S)) =
        ⟨l₁ * a * l₁⁻¹ * a⁻¹, hSP he⟩ * ⟨a, haP⟩ := Subtype.ext heq
    rw [e]
    exact perm_mul_ne_one hF he ha1 ha3
  · exact perm_cube_of_normalizer_odd hF htN (odd_orderOf_conj _ _ haodd)
  · have e : (l₁ * k * l₂)⁻¹ * (l₁ * a * l₁⁻¹) * (l₁ * k * l₂) =
        (l₂⁻¹ * (k⁻¹ * a * k) * l₂ * (k⁻¹ * a * k)⁻¹) * (k⁻¹ * a * k) := by group
    rw [e]
    exact (K1 ⊔ S).mul_mem (hSP hc₂) hbP

end CFSG.Quasithin.SzVB
