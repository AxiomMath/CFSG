module

public import CFSG.Quasithin.H13.L32AC52c
public import CFSG.Quasithin.Vol2.Ch9Sec3FFBBar
public import CFSG.Quasithin.H13.A7Nat1238QTabA314

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm

theorem card_stab_five_le {S : Finset (Fin 7)} (hS : S.card = 5) :
    Nat.card {σ : Perm (Fin 7) // sign σ = 1 ∧ ∀ i ∈ S, σ i ∈ S} ≤ 120 := by
  classical
  have hiff : ∀ σ : Perm (Fin 7), (∀ i ∈ S, σ i ∈ S) → ∀ x, x ∈ S ↔ σ x ∈ S := by
    intro σ hσ x
    refine ⟨hσ x, fun hx => ?_⟩
    have himg : S.image σ = S :=
      Finset.eq_of_subset_of_card_le (fun y hy => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact hσ z hz) (Finset.card_image_of_injective _ σ.injective).symm.le
    rw [← himg] at hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    rwa [σ.injective hzx] at hz
  let f : {σ : Perm (Fin 7) // sign σ = 1 ∧ ∀ i ∈ S, σ i ∈ S} → Perm {x // x ∈ S} :=
    fun σ => (σ.1).subtypePerm fun x => (hiff σ.1 σ.2.2 x).symm
  have hc : (Finset.univ \ S).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hS]
  obtain ⟨a, b, hab, hcab⟩ := Finset.card_eq_two.mp hc
  have hmem : ∀ x, x ∉ S ↔ x = a ∨ x = b := fun x => by
    have : x ∈ Finset.univ \ S ↔ x ∈ ({a, b} : Finset (Fin 7)) := by rw [hcab]
    simpa using this
  have hf : Function.Injective f := by
    rintro ⟨σ, hσ1, hσS⟩ ⟨τ, hτ1, hτS⟩ h
    have hst : ∀ x ∈ S, σ x = τ x := fun x hx => by
      have := congrArg (fun π : Perm {x // x ∈ S} => (π ⟨x, hx⟩ : Fin 7)) h
      simpa [f] using this
    set ρ := τ⁻¹ * σ with hρ
    have hρS : ∀ x ∈ S, ρ x = x := fun x hx => by
      rw [hρ, Perm.mul_apply, hst x hx]
      exact τ.symm_apply_apply x
    have hρ1 : sign ρ = 1 := by rw [hρ, map_mul, map_inv, hσ1, hτ1, inv_one, one_mul]
    have hout : ∀ x, x ∉ S → ρ x ∉ S := fun x hx hρx => by
      have h1 : ρ (ρ x) = ρ x := hρS _ hρx
      rw [ρ.injective h1] at hρx
      exact hx hρx
    have ha := (hmem _).mp (hout a ((hmem a).mpr (Or.inl rfl)))
    have hb := (hmem _).mp (hout b ((hmem b).mpr (Or.inr rfl)))
    have hρeq : ρ = 1 := by
      rcases ha with ha | ha
      · have hb' : ρ b = b := by
          rcases hb with hb | hb
          · exact absurd (ρ.injective (hb.trans ha.symm)) (Ne.symm hab)
          · exact hb
        ext x
        by_cases hx : x ∈ S
        · simp [hρS x hx]
        · rcases (hmem x).mp hx with rfl | rfl
          · simp [ha]
          · simp [hb']
      · exfalso
        have hb' : ρ b = a := by
          rcases hb with hb | hb
          · exact hb
          · exact absurd (ρ.injective (hb.trans ha.symm)) (Ne.symm hab)
        have hsw : ρ = swap a b := by
          ext x
          by_cases hx : x ∈ S
          · have hxa : x ≠ a := fun h => (hmem x).not.mp (not_not.mpr hx) (Or.inl h)
            have hxb : x ≠ b := fun h => (hmem x).not.mp (not_not.mpr hx) (Or.inr h)
            rw [hρS x hx, swap_apply_of_ne_of_ne hxa hxb]
          · rcases (hmem x).mp hx with rfl | rfl
            · rw [ha, swap_apply_left]
            · rw [hb', swap_apply_right]
        rw [hsw, sign_swap hab] at hρ1
        exact absurd hρ1 (by decide)
    apply Subtype.ext
    exact (inv_mul_eq_one.mp hρeq).symm
  calc Nat.card {σ : Perm (Fin 7) // sign σ = 1 ∧ ∀ i ∈ S, σ i ∈ S}
      ≤ Nat.card (Perm {x // x ∈ S}) := Nat.card_le_card_of_injective f hf
    _ = 120 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe, hS]
      rfl

theorem mem_of_card_le_two_mul {X : Type*} [Group X] [Finite X] {A N : Subgroup X} (hAN : A ≤ N)
    (hc : Nat.card N ≤ 2 * Nat.card A) {g : X} (hg : g ∈ N) (hodd : Odd (orderOf g)) :
    g ∈ A := by
  set A' := A.subgroupOf N with hA'
  have hcard : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hmul : A'.index * Nat.card A' = Nat.card N := A'.index_mul_card
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hidx : A'.index ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 3 * Nat.card A ≤ A'.index * Nat.card A' := by
      rw [hcard]
      exact Nat.mul_le_mul_right _ hlt
    omega
  have hi0 : A'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hg' : (⟨g, hg⟩ : ↥N) ∈ A' := by
    rcases (show A'.index = 1 ∨ A'.index = 2 by omega) with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top _
    · have hsq := Subgroup.mul_self_mem_of_index_two h2 ⟨g, hg⟩
      obtain ⟨k, hk⟩ := hodd
      have he : (⟨g, hg⟩ : ↥N) = (⟨g, hg⟩ * ⟨g, hg⟩) ^ (k + 1) := by
        rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ]
        have h1 : (⟨g, hg⟩ : ↥N) ^ orderOf g = 1 :=
          Subtype.ext (by simp [pow_orderOf_eq_one])
        rw [h1, one_mul]
      rw [he]
      exact A'.pow_mem hsq _
  exact Subgroup.mem_subgroupOf.mp hg'

theorem mem_of_stabilizesFive {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} (hBL : B ≤ L)
    (hB : Nat.card B = 60) {f : ↥L →* Perm (Fin 7)} (hf : Function.Injective f)
    (hfr : f.range = alternatingGroup (Fin 7)) {S : Finset (Fin 7)} (hS : S.card = 5)
    (hN : ∀ g : ↥L, (g : Q) ∈ Subgroup.normalizer (B : Set Q) ↔ ∀ x ∈ S, f g x ∈ S)
    {g : ↥L} (hg : (g : Q) ∈ Subgroup.normalizer (B : Set Q)) (hodd : Odd (orderOf g)) :
    (g : Q) ∈ B := by
  set N : Subgroup ↥L := (Subgroup.normalizer (B : Set Q)).subgroupOf L with hNdef
  set A : Subgroup ↥L := B.subgroupOf L with hAdef
  have hAN : A ≤ N := fun a ha =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp ha))
  have hA : Nat.card A = 60 := by
    rw [← hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hsign : ∀ n : ↥L, sign (f n) = 1 := fun n => by
    have : f n ∈ f.range := ⟨n, rfl⟩
    rw [hfr] at this
    exact Perm.mem_alternatingGroup.mp this
  let φ : ↥N → {σ : Perm (Fin 7) // sign σ = 1 ∧ ∀ i ∈ S, σ i ∈ S} := fun n =>
    ⟨f n, hsign n, (hN n).mp (Subgroup.mem_subgroupOf.mp n.2)⟩
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (hf (congrArg Subtype.val h))
  have hNc : Nat.card N ≤ 120 := (Nat.card_le_card_of_injective φ hφ).trans (card_stab_five_le hS)
  have hgN : g ∈ N := Subgroup.mem_subgroupOf.mpr hg
  exact Subgroup.mem_subgroupOf.mp (mem_of_card_le_two_mul hAN (by omega) hgN hodd)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_odd_of_sup_pGroup {K P : Subgroup G} (hP : IsPGroup 2 P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ P)
    (hodd : Odd (orderOf x)) : x ∈ K := by
  obtain ⟨k, hk, p, hp, rfl⟩ := CFSG.QuasithinUnique.Setup.Family.mem_sup_of_le_normalizer hPK hx
  have hpow : ∀ j : ℕ, (k * p) ^ j * (p ^ j)⁻¹ ∈ K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : p ^ j * k * (p ^ j)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hPK hp) j) k).mp hk
      have e : (k * p) ^ (j + 1) * (p ^ (j + 1))⁻¹ =
          ((k * p) ^ j * (p ^ j)⁻¹) * (p ^ j * k * (p ^ j)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact K.mul_mem ih hc
  obtain ⟨m, hm⟩ := hP ⟨p, hp⟩
  have hpm : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hxK : (k * p) ^ 2 ^ m ∈ K := by
    have := hpow (2 ^ m)
    rwa [hpm, inv_one, mul_one] at this
  have hcop : Nat.Coprime (2 ^ m) (orderOf (k * p)) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd)
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact K.pow_mem hxK u

variable {T L V : Subgroup G}

theorem eq_of_card_cStar_eq (h : Hyp147 G T L V) {Y K K₁ : Subgroup G} (hTY : T ≤ Y)
    (hK₁ : K₁ ∈ cComp Y) (hKK₁ : K ≤ K₁) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hc : Nat.card (cStar K) = Nat.card (cStar K₁)) : K₁ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := (card_dvd_of_le hKK₁).2 hc
  have hNT : pCoreOf 2 K₁ ≤ T :=
    (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK₁)).trans
      (L32A.pCoreOf_le_of_le h hTY)
  have hT2 : IsPGroup 2 T := (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTY).2.1
  exact Vol2.Ch11.SecA.eq_of_le_sup_of_perfect hKK₁ (perfect_of_mem_cComp hK₁) hT2 hTK
    (hle.trans (sup_le_sup_left hNT K))

omit [Finite G] in
theorem list1222_of_quot {X : Type} [Group X] {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) : A7.List1222 X := by
  refine Or.inr ⟨n, h5, h8, e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun x hx => ?_⟩
  have h1 : QuotientGroup.mk' (Subgroup.center X) x = 1 :=
    e.injective (by rw [map_one]; exact hx)
  exact (QuotientGroup.eq_one_iff x).1 h1

omit [Finite G] in
theorem list1222_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : A7.List1222 X) :
    A7.List1222 Y := by
  rcases h with h | ⟨n, h5, h8, φ, hφ, hk⟩
  · left
    rwa [← Nat.card_congr e.toEquiv]
  · refine Or.inr ⟨n, h5, h8, φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective,
      fun y hy => ?_⟩
    have hz : e.symm y ∈ Subgroup.center X := hk hy
    refine Subgroup.mem_center_iff.mpr fun z => e.symm.injective ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hz (e.symm z)

theorem a314_two_of_list
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h314 : A314Facts) {Y K K₁ : Subgroup G}
    (hSQ : SQTKGroup ↥Y) (hT : IsSylowTwoOf T Y) (hKY : K ≤ Y) (hKl : K ∈ lFamily T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hA5 : IsAlt 5 (cStar K)) (hK₁ : K₁ ∈ cComp Y)
    (hYK₁ : Y ≤ Subgroup.normalizer (K₁ : Set G)) (hlt : K < K₁)
    (hq₁ : CFSG.IsQuasisimple (cStar K₁)) (hlist : A7.List1222 (cStar K₁)) :
    Nonempty (cStar K₁ ≃* ↥(modO2Image Y K₁)) ∧ IsAlt 5 ↥(modO2Image Y K) ∧
      (IsAlt 7 ↥(modO2Image Y K₁) ∨ IsHat ↥(modO2Image Y K₁) ↥(alternatingGroup (Fin 7))) ∧
      StabilizesFivePoints (modO2Image Y K) (modO2Image Y K₁) := by
  obtain ⟨e5⟩ := hA5
  have hA : Nonempty (O2Q K ≃* alternatingGroup (Fin 5)) := ⟨(cStarEquiv K).symm.trans e5⟩
  obtain ⟨hltb, hst⟩ := Ch9.FFB.a314_bar h36 h312 h314 hSQ hT hKY hKl hTK hA hK₁ hlt
  obtain ⟨eL⟩ := Ch9.FFB.nonempty_o2q_equiv hSQ hK₁ hYK₁
  set e : cStar K₁ ≃* ↥(modO2Image Y K₁) := (cStarEquiv K₁).trans eL with he
  have hqL : CFSG.IsQuasisimple ↥(modO2Image Y K₁) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq₁
  have hZL : Odd (Nat.card (Subgroup.center ↥(modO2Image Y K₁))) := by
    rw [← card_center_eq_of_mulEquiv e]
    exact odd_card_center_cStar K₁
  obtain ⟨h5, h7, hst5⟩ := A7.a314_case_two_of_list hst hltb hqL hZL (list1222_congr e hlist)
  exact ⟨⟨e⟩, h5, h7, hst5⟩

end CFSG.Quasithin.H13.L32A.C
