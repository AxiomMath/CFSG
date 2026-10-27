module

public import CFSG.Quasithin.H13.L32NLem14324j
public import CFSG.Quasithin.H13.L32NLem14324k
public import CFSG.Quasithin.H13.L32NLem14323b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

theorem inv_mul_mem_of_card {G : Type} [Group G] [Finite G] {K H : Subgroup G} (hKH : K ≤ H)
    (hcard : Nat.card H = 2 * Nat.card K) {x z : G} (hx : x ∈ H) (hz : z ∈ H) (hxK : x ∉ K)
    (hzK : z ∉ K) : x⁻¹ * z ∈ K := by
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hidx : (K.subgroupOf H).index = 2 := by
    have h1 := (K.subgroupOf H).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv, hcard] at h1
    have h2 : Nat.card K * (K.subgroupOf H).index = Nat.card K * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hx⟩ : ↥H)⁻¹) (b := ⟨z, hz⟩))
  have hx' : (⟨x, hx⟩ : ↥H)⁻¹ ∉ K.subgroupOf H := fun hm => hxK (by
    have := K.inv_mem (Subgroup.mem_subgroupOf.mp hm)
    simpa using this)
  have hz' : (⟨z, hz⟩ : ↥H) ∉ K.subgroupOf H := fun hm => hzK (Subgroup.mem_subgroupOf.mp hm)
  have := h.mpr (iff_of_false hx' hz')
  exact Subgroup.mem_subgroupOf.mp this

variable {G : Type} [Group G] [Finite G]

theorem false_of_concl8S8
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h12813 : Lemma12_8_13) (h14312 : Lemma14312One) (hFixS : G11.SzG11S.TheoremG112FixS)
    {T L V : Subgroup G} (h : Hyp14310One G T L V) (hlt : fsuV1 T V < centerOf (fsuU T V))
    {V₂ : Subgroup G} {g : G} (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgN : g ∉ l32nH T V) (D : HatModelU (fsuU T V))
    (h8 : G11.G112Concl8S8 D.B (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g))) :
    False := by
  classical
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨-, hV8, hLTV, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  have hlt2 : V₂ < V := lt_of_le_of_ne hV₂.1.1 fun he => by rw [he] at hV₂4; omega
  obtain ⟨c, hcV, hc2⟩ := IsConcreteLE.exists_of_lt hlt2
  have haV : a ∈ V := hV₂.1.1 haV₂
  obtain ⟨l, -, -, hlH, hla⟩ : ∃ l ∈ L, l ^ 3 = 1 ∧ l ∈ l32nH T V ∧ l * a * l⁻¹ = c := by
    obtain ⟨_, S⟩ := L14332.exists_setting h1332 h1334 h1222 h hV₂
    obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
    have hzV₂ : z ∈ V₂ := hV₂.2 hz
    obtain ⟨l, hlL, hl3, hlz, hla, -⟩ := S.exists_rot (Subgroup.mem_inf.mp hz).1 haV hcV
      (fun he => ha1 (by rw [he]; exact one_mem _)) (fun he => hc2 (by rw [he]; exact one_mem _))
      (fun he => ha1 (by rw [he]; exact hz)) (fun he => hc2 (by rw [he]; exact hzV₂))
      (fun he => hc2 (by rw [← he]; exact haV₂))
      (fun he => hc2 (by rw [he]; exact V₂.mul_mem hzV₂ haV₂))
    exact ⟨l, hlL, hl3, S.mem_g1 hz hz1 hlz, hla⟩
  obtain ⟨a₀, H, -, -, -⟩ :=
    data_of h1332 h1334 h1222 h12213 h12813 h14312 hFixS h hlt hV₂ hgP hgN D
  have hB := H.toG101Hyp
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
  have hVZ := lemma12_8_8_three h1222 h12213 hs
  have hV1Z : ∀ v ∈ fsuV1 T V, v ∈ centerOf (fsuU T V) := fun v hv => by
    have : v ∈ V ⊓ zU128 V (fsuV1 T V) := by rw [hVZ]; exact hv
    exact this.2
  have hπV : ∀ v ∈ V, D.π v = 0 → v ∈ fsuV1 T V := by
    intro v hv h0
    have hvZ := (L128A.HatU.π_eq_zero_iff D (hVU hv)).mp h0
    rw [← hVZ]
    exact ⟨hv, hvZ⟩
  have hπmul : ∀ u ∈ V, ∀ w ∈ V, D.π (u * w) = D.π u + D.π w := fun u hu w hw =>
    D.π_mul u (hVU hu) w (hVU hw)
  have hV1V2 : fsuV1 T V ≤ V₂ := hV₂.2
  have hcard12 : Nat.card V₂ = 2 * Nat.card (fsuV1 T V) := by rw [hV₂4, hV1]
  have hcard2 : Nat.card V = 2 * Nat.card V₂ := by rw [hV8, hV₂4]
  have hπa : D.π a ≠ 0 := fun h0 => ha1 (hπV a haV h0)
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
  have hTH : T ≤ l32nH T V := h.le_l32nH hV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := hV₂.1.2.2
  have hTV₁ : T ≤ Subgroup.normalizer (fsuV1 T V : Set G) := (h.isTSub_fsuV1 hV).2.2
  have hconj : ∀ {Y : Subgroup G} {t : G}, t ∈ Subgroup.normalizer (Y : Set G) → ∀ y,
      (t * y * t⁻¹ ∈ Y ↔ y ∈ Y) := fun ht y => (Subgroup.mem_normalizer_iff.mp ht y).symm
  have hTa : ∀ t ∈ D.img T, t (D.π a) = D.π a := by
    intro t ht
    obtain ⟨y, hy, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp ht
    rw [D.ρ_π ⟨y, hyN⟩ a (hVU haV)]
    have h1 : y * a * y⁻¹ ∈ V₂ := (hconj (hTV₂ hy) a).mpr haV₂
    have h2 : y * a * y⁻¹ ∉ fsuV1 T V := fun hm => ha1 ((hconj (hTV₁ hy) a).mp hm)
    have h3 := inv_mul_mem_of_card hV1V2 hcard12 h1 haV₂ h2 ha1
    exact (D.π_eq_iff _ (hVU (hV₂.1.1 h1)) _ (hVU haV)).mpr (hV1Z _ h3)
  have hTc : ∀ t ∈ D.img T, t (D.π c) = D.π c ∨ t (D.π c) = D.π c + D.π a := by
    intro t ht
    obtain ⟨y, hy, hyN, rfl⟩ := (L128A.HatU.mem_img D).mp ht
    rw [D.ρ_π ⟨y, hyN⟩ c (hVU hcV)]
    have h1 : y * c * y⁻¹ ∈ V := (hconj (hTV hy) c).mpr hcV
    have h2 : y * c * y⁻¹ ∉ V₂ := fun hm => hc2 ((hconj (hTV₂ hy) c).mp hm)
    have h3 := inv_mul_mem_of_card hV₂.1.1 hcard2 hcV h1 hc2 h2
    have e : y * c * y⁻¹ = c * (c⁻¹ * (y * c * y⁻¹)) := by group
    rw [e, hπmul _ hcV _ (hV₂.1.1 h3)]
    by_cases hq : c⁻¹ * (y * c * y⁻¹) ∈ fsuV1 T V
    · left
      rw [(L128A.HatU.π_eq_zero_iff D (hVU (hV₂.1.1 h3))).mpr (hV1Z _ hq), add_zero]
    · right
      have h4 := inv_mul_mem_of_card hV1V2 hcard12 haV₂ h3 ha1 hq
      rw [← (D.π_eq_iff _ (hVU haV) _ (hVU (hV₂.1.1 h3))).mpr (hV1Z _ h4)]
  have hΓcard : Nat.card (D.img (l32nH T V)) = 40320 := by
    obtain ⟨φ⟩ := h8.2.1
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hTΓ : D.img T ≤ D.img (l32nH T V) := L14323.img_mono D hTH
  have hTcard : Nat.card (D.img T) = 128 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hT2 : IsPGroup 2 ↥(D.img T) :=
      (h.fsu.sylow.1.comap_of_injective (Subgroup.normalizer (fsuU T V : Set G)).subtype
        (Subgroup.normalizer (fsuU T V : Set G)).subtype_injective).map D.ρ
    have hodd : Odd ((D.img T).relIndex (D.img (l32nH T V))) := by
      have hdvd := L14332.relIndex_img_dvd D hTH hN
      have hsyl := (h.isSylowTwoOf_l32nH hV).2.2
      have hodd : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (by
        rcases Nat.even_or_odd (T.relIndex (l32nH T V)) with he | ho
        · exact absurd (even_iff_two_dvd.mp he) hsyl
        · exact Nat.odd_iff.mp ho)
      exact Odd.of_dvd_nat hodd hdvd
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
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
    rw [L14411.matOf_mulVec, hTa t ht]
  · rintro _ ⟨t, ht, rfl⟩
    rw [L14411.matOf_mulVec, ← map_add]
    rcases hTc t ht with h0 | h0
    · left; rw [h0]
    · right; rw [h0]
  · left
    rw [L14411.matOf_mulVec, hya]

theorem cases_of_inputs''
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12813 : Lemma12_8_13)
    (h14312 : Lemma14312One) (hFixS : G11.SzG11S.TheoremG112FixS)
    (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) (V₂ : Subgroup G) (g : G)
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V)
    (D : HatModelU (fsuU T V)) (hd : 6 ≤ Module.finrank (ZMod 2) D.V) :
    G112Concl6 (D.img (l32nH T V)) ∨ G112Concl5 D.B (D.img (l32nH T V)) ∨
      G11.SzG11S.G112Concl13S (D.img (l32nH T V)) := by
  rcases cases_of_inputs' h1332 h1334 h1222 h12213 h12813 h14312 hFixS G T L V h hlt V₂ g hV₂
    hgP hgN D hd with h6 | h5 | h8 | h13
  · exact Or.inl h6
  · exact Or.inr (Or.inl h5)
  · exact (false_of_concl8S8 h1332 h1334 h1222 h12213 h12813 h14312 hFixS h hlt hV₂ hgP hgN D
      h8).elim
  · exact Or.inr (Or.inr h13)

end L14324

end CFSG.Quasithin.H13
