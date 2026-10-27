module

public import CFSG.Quasithin.H13.L32NLem1442a
public import CFSG.Quasithin.H13.L32NLem14324l

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

theorem false_of_concl8S8
    (h8 : G11.G112Concl8S8 D.B (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g))) :
    False := by
  classical
  obtain ⟨_, S⟩ := C.base.set14
  have hV₂ := C.base.plane
  have hV1 := C.card_V1
  have hV8 : Nat.card V = 8 := S.card_V
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt2 : V₂ < V := lt_of_le_of_ne hV₂.1.1 fun he => by rw [he] at hV₂4; omega
  obtain ⟨c, hcV, hc2⟩ := IsConcreteLE.exists_of_lt hlt2
  have haV₂ := C.aV₂
  have ha1 := C.a1
  have haV : a ∈ V := hV₂.1.1 haV₂
  obtain ⟨l, -, -, hlH, hla⟩ : ∃ l ∈ L, l ^ 3 = 1 ∧ l ∈ l32nH T V ∧ l * a * l⁻¹ = c := by
    obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
    have hzV₂ : z ∈ V₂ := hV₂.2 hz
    obtain ⟨l, hlL, hl3, hlz, hla, -⟩ := S.exists_rot (Subgroup.mem_inf.mp hz).1 haV hcV
      (fun he => ha1 (by rw [he]; exact one_mem _)) (fun he => hc2 (by rw [he]; exact one_mem _))
      (fun he => ha1 (by rw [he]; exact hz)) (fun he => hc2 (by rw [he]; exact hzV₂))
      (fun he => hc2 (by rw [← he]; exact haV₂))
      (fun he => hc2 (by rw [he]; exact V₂.mul_mem hzV₂ haV₂))
    exact ⟨l, hlL, hl3, S.mem_g1 hz hz1 hlz, hla⟩
  have hB := C.g111.toG101Hyp
  obtain ⟨A, I, I', x, d8, -, hIiso⟩ := SzN28.s8Data_iso_of_concl8 hB.X_le hB.X_sq h8
  have hxΓ := d8.x_mem
  have F : S8Tr.Frame D.B I I' :=
    { alt := hB.alt
      nd := hB.nondegenerate
      compl := d8.compl
      iso := hIiso
      iso' := by
        rw [d8.I'_eq]
        rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩
        exact (hB.isometry x hxΓ i i').trans (hIiso i hi i' hi')
      rank := d8.rank4
      rank' := d8.rank4' }
  have hN := L14332.l32nH_le_normalizer_fsuU T V
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV1Z : ∀ v ∈ fsuV1 T V, v ∈ centerOf (fsuU T V) := fun v hv => by
    rw [C.base.zU]
    exact hv
  have hπV : ∀ v ∈ V, D.π v = 0 → v ∈ fsuV1 T V := by
    intro v hv h0
    have hvZ := (L128A.HatU.π_eq_zero_iff D (hVU hv)).mp h0
    rwa [C.base.zU] at hvZ
  have hπmul : ∀ u ∈ V, ∀ w ∈ V, D.π (u * w) = D.π u + D.π w := fun u hu w hw =>
    D.π_mul u (hVU hu) w (hVU hw)
  have hV1V2 : fsuV1 T V ≤ V₂ := hV₂.2
  have hcard12 : Nat.card V₂ = 2 * Nat.card (fsuV1 T V) := by rw [hV₂4, hV1]
  have hcard2 : Nat.card V = 2 * Nat.card V₂ := by rw [hV8, hV₂4]
  have hπa : D.π a ≠ 0 := C.πa_ne
  have hπc : D.π c ≠ 0 := fun h0 => hc2 (hV1V2 (hπV c hcV h0))
  have hπca : D.π c ≠ D.π a := by
    intro he
    have h1 : D.π (a⁻¹ * c) = 0 := by
      rw [hπmul _ (V.inv_mem haV) _ hcV, L128A.HatU.π_inv D (hVU haV), he, neg_add_cancel]
    have h2 := hπV _ (V.mul_mem (V.inv_mem haV) hcV) h1
    apply hc2
    have : c = a * (a⁻¹ * c) := by group
    rw [this]
    exact V₂.mul_mem haV₂ (hV1V2 h2)
  have hTH : T ≤ l32nH T V := C.base.TH
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := S.TV
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := hV₂.1.2.2
  have hTV₁ : T ≤ Subgroup.normalizer (fsuV1 T V : Set G) := S.T_V1
  have hconj : ∀ {Y : Subgroup G} {t : G}, t ∈ Subgroup.normalizer (Y : Set G) → ∀ y,
      (t * y * t⁻¹ ∈ Y ↔ y ∈ Y) := fun ht y => (Subgroup.mem_normalizer_iff.mp ht y).symm
  have hTc : ∀ t ∈ D.img T, t (D.π c) = D.π c ∨ t (D.π c) = D.π c + D.π a := by
    intro t ht
    obtain ⟨y, hy, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp ht
    rw [D.ρ_π ⟨y, hyN⟩ c (hVU hcV)]
    have h1 : y * c * y⁻¹ ∈ V := (hconj (hTV hy) c).mpr hcV
    have h2 : y * c * y⁻¹ ∉ V₂ := fun hm => hc2 ((hconj (hTV₂ hy) c).mp hm)
    have h3 := L14324.inv_mul_mem_of_card hV₂.1.1 hcard2 hcV h1 hc2 h2
    have e : y * c * y⁻¹ = c * (c⁻¹ * (y * c * y⁻¹)) := by group
    rw [e, hπmul _ hcV _ (hV₂.1.1 h3)]
    by_cases hq : c⁻¹ * (y * c * y⁻¹) ∈ fsuV1 T V
    · left
      rw [(L128A.HatU.π_eq_zero_iff D (hVU (hV₂.1.1 h3))).mpr (hV1Z _ hq), add_zero]
    · right
      have h4 := L14324.inv_mul_mem_of_card hV1V2 hcard12 haV₂ h3 ha1 hq
      rw [← (D.π_eq_iff _ (hVU haV) _ (hVU (hV₂.1.1 h3))).mpr (hV1Z _ h4)]
  have hΓcard : Nat.card (D.img (l32nH T V)) = 40320 := by
    obtain ⟨φ⟩ := h8.2.1
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hsyl := C.isSylow
  have hTΓ : D.img T ≤ D.img (l32nH T V) := hsyl.1
  have hTcard : Nat.card (D.img T) = 128 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hsyl.2.1.exists_card_eq
    have hodd := C.Todd
    have hmul := Subgroup.relIndex_mul_card (H := D.img T) (K := D.img (l32nH T V))
    rw [inf_eq_left.mpr hTΓ, hk, hΓcard] at hmul
    obtain ⟨r, hr⟩ := hodd
    rw [hr] at hmul
    have hk15 : k ≤ 15 := by
      by_contra hk'
      push Not at hk'
      have : 2 ^ 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk'
      have : 2 ^ k ≤ (2 * r + 1) * 2 ^ k := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [hk]
    interval_cases k <;> norm_num at hmul ⊢ <;> omega
  have hlN := hN hlH
  have hyΓ : D.ρ ⟨l, hlN⟩ ∈ D.img (l32nH T V) := L128A.HatU.rho_mem_img D hlH hlN
  have hya : D.ρ ⟨l, hlN⟩ (D.π a) = D.π c := by
    rw [D.ρ_π ⟨l, hlN⟩ a (hVU haV)]
    exact congrArg D.π hla
  obtain ⟨e, he⟩ := F.exists_coord_le_s8 d8 hB.isometry
  refine S8Tr.false_of_sylow_plane (T' := (D.img T).map (L14411.matOf e)) ?_ ?_
    (w := e (D.π a)) (p := e (D.π c)) ?_ ?_ ?_ ?_ ?_ (he _ hyΓ) ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact he t (hTΓ ht)
  · rw [Subgroup.card_map_of_injective (L14411.matOf_injective e)]
    exact hTcard
  · exact fun h0 => hπa (e.injective (h0.trans e.map_zero.symm))
  · exact fun h0 => hπc (e.injective (h0.trans e.map_zero.symm))
  · exact fun h0 => hπca (e.injective h0)
  · rintro _ ⟨t, ht, rfl⟩
    rw [L14411.matOf_mulVec, C.fix_T t ht]
  · rintro _ ⟨t, ht, rfl⟩
    rw [L14411.matOf_mulVec, ← map_add]
    rcases hTc t ht with h0 | h0
    · left; rw [h0]
    · right; rw [h0]
  · left
    rw [L14411.matOf_mulVec, hya]

end Ctx

end L1442

end CFSG.Quasithin.H13
