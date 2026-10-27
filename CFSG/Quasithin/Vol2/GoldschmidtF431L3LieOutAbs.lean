module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieOutGrp
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Out

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

section Hyp

structure L3OutHyp {P H : Type} [Group P] [Group H] (Φ : P →* H) (U R₁ R₂ : Subgroup P)
    (q : ℕ) : Prop where
  two_le : 2 ≤ q
  card_Z : Nat.card (centerOf U) = q
  card_R₁ : Nat.card R₁ = q ^ 2
  noswap : ∀ h ∈ Subgroup.normalizer ((U.map Φ : Subgroup H) : Set H),
    h ∈ Subgroup.normalizer ((R₁.map Φ : Subgroup H) : Set H) ∧
      h ∈ Subgroup.normalizer ((R₂.map Φ : Subgroup H) : Set H)
  cyc : ∀ X : Subgroup H, X ≤ Subgroup.normalizer ((U.map Φ : Subgroup H) : Set H) →
    IsPGroup 2 X → X ⊓ Φ.range = ⊥ → IsCyclic X ∧ Nat.card X < q
  bound : ∀ h ∈ Subgroup.normalizer ((U.map Φ : Subgroup H) : Set H), (∃ k : ℕ, orderOf h = 2 ^ k) →
    h ∉ Φ.range →
    (∀ B : Subgroup H, B ≤ R₁.map Φ → (∀ g ∈ B, h * g = g * h) → Nat.card B ≤ q) ∧
    (∀ B : Subgroup H, B ≤ R₂.map Φ → (∀ g ∈ B, h * g = g * h) → Nat.card B ≤ q) ∧
    (∀ B : Subgroup H, B ≤ (centerOf U).map Φ → (∀ g ∈ B, h * g = g * h) →
      Nat.card B ^ 2 ≤ q)

end Hyp

section Lemmas

variable {H : Type} [Group H] [Finite H]

theorem exists_fixed_not_mem {V Z : Subgroup H} {f : H} {q : ℕ}
    (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x * x = 1) (hf2 : f * f = 1)
    (hf : ∀ v ∈ V, f * v * f⁻¹ ∈ V) (hcardV : Nat.card V = q ^ 2) (hq : 2 ≤ q)
    (hZ : ∀ B : Subgroup H, B ≤ Z → (∀ g ∈ B, f * g = g * f) → Nat.card B ^ 2 ≤ q) :
    ∃ a ∈ V, f * a = a * f ∧ a ∉ Z := by
  by_contra hcon
  push Not at hcon
  have hBZ : V ⊓ Subgroup.centralizer ({f} : Set H) ≤ Z := by
    intro a ha
    have ha' : a ∈ Subgroup.centralizer ({f} : Set H) := ha.2
    exact hcon a ha.1 (Subgroup.mem_centralizer_singleton_iff.mp ha').symm
  have h1 := hZ _ hBZ (fun g hg => by
    have hg' : g ∈ Subgroup.centralizer ({f} : Set H) := hg.2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hg').symm)
  have h2 := card_le_card_inf_centralizer_sq hV hV2 hf2 hf
  rw [hcardV] at h2
  nlinarith

end Lemmas

section Lift

open CFSG.LieType.BorelTits CFSG.QuasithinUnique.Borel252

theorem isSylowTwoOf_map_range {P H : Type} [Group P] [Group H] (Φ : P →* H)
    (hΦ : Function.Injective Φ) {U : Subgroup P} (hU : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map Φ) Φ.range := by
  refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_le_range Φ U) (hU.2.1.map Φ) ?_
  have h := Subgroup.relIndex_map_map_of_injective (f := Φ) U ⊤ hΦ
  rw [← MonoidHom.range_eq_map] at h
  rw [h]
  exact F7.isSylowTwoOf_odd_relIndex hU

theorem exists_l3OutDatum_of_data {P H : Type} [Group P] [Group H] [Finite P] [Finite H]
    (Φ : P →* H) (hΦ : Function.Injective Φ) [hΦn : Φ.range.Normal]
    (heven : ¬ Odd Φ.range.index) {U R₁ R₂ B₀ : Subgroup P} {s₁ s₂ : P}
    (hD : L3DData U R₁ R₂ B₀ s₁ s₂) {q : ℕ} (hO : L3OutHyp Φ U R₁ R₂ q) (N₁ N₂ : Subgroup H)
    (h₁ : N₁ = Subgroup.normalizer ((R₁.map Φ : Subgroup H) : Set H))
    (h₂ : N₂ = Subgroup.normalizer ((R₂.map Φ : Subgroup H) : Set H)) :
    Nonempty (L3OutDatum N₁ N₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Subgroup H := Φ.range with hI
  set T0 : Subgroup H := U.map Φ with hT0
  set Q₁ : Subgroup H := R₁.map Φ with hQ₁
  set Q₂ : Subgroup H := R₂.map Φ with hQ₂
  set B₀' : Subgroup H := B₀.map Φ with hB₀'
  have hIn : I.Normal := hΦn
  have hSylI : IsSylowTwoOf T0 I := isSylowTwoOf_map_range Φ hΦ hD.borel.sylow
  have hTp : IsPGroup 2 T0 := hSylI.2.1
  have hcenT : centerOf T0 = (centerOf U).map Φ := centerOf_map_of_injective Φ hΦ U
  have hcardZ : Nat.card (centerOf T0) = q := by
    rw [hcenT, Subgroup.card_map_of_injective hΦ]; exact hO.card_Z
  have hUN₁ : U ≤ Subgroup.normalizer (R₁ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₁.le
  have hUN₂ : U ≤ Subgroup.normalizer (R₂ : Set P) :=
    Subgroup.le_normalizer.trans hD.borel.lt₂.le
  have hTN₁ : T0 ≤ N₁ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [h₁]; exact map_mem_normalizer_map Φ (hUN₁ hu)
  have hTN₂ : T0 ≤ N₂ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [h₂]; exact map_mem_normalizer_map Φ (hUN₂ hu)
  have hF : Frame T0 Q₁ Q₂ := Frame.map Φ hΦ hD.frame
  have hTsup : T0 = Q₁ ⊔ Q₂ := by rw [hT0, hQ₁, hQ₂, ← Subgroup.map_sup, hD.borel.sup]
  have hN_eq : N₁ ⊓ N₂ = Subgroup.normalizer (T0 : Set H) := by
    apply le_antisymm
    · intro n hn
      rw [hTsup]
      exact mem_normalizer_sup (h₁ ▸ hn.1) (h₂ ▸ hn.2)
    · intro n hn
      obtain ⟨hn1, hn2⟩ := hO.noswap n hn
      exact ⟨by rw [h₁]; exact hn1, by rw [h₂]; exact hn2⟩
  have hB₀N : B₀' ≤ Subgroup.normalizer (T0 : Set H) := by
    rintro _ ⟨b, hb, rfl⟩
    exact map_mem_normalizer_map Φ (hD.B₀_le hb)
  have hB₀I : B₀' ≤ I := Subgroup.map_le_range Φ B₀
  have hodd₀ : Odd (Nat.card B₀') := by
    rw [hB₀', Subgroup.card_map_of_injective hΦ]; exact hD.B₀_odd
  have hC : ∀ x ∈ T0, (∀ b ∈ B₀', x * b = b * x) → x = 1 := by
    rintro _ ⟨u, hu, rfl⟩ hcomm
    have : u = 1 := hD.centS u hu (fun b hb => hΦ (by
      rw [map_mul, map_mul]; exact hcomm _ (Subgroup.mem_map_of_mem Φ hb)))
    rw [this, map_one]
  have hUp : IsPGroup 2 U := hD.borel.sylow.2.1
  have hcardP : Nat.card (Subgroup.normalizer (U : Set P)) = Nat.card U * Nat.card B₀ :=
    card_eq_mul_of_split Subgroup.le_normalizer hD.B₀_le
      (fun x hx hxB => eq_one_of_pgroup_of_odd hUp hD.B₀_odd hx hxB) hD.mul
  have hcard : Nat.card ↥(Subgroup.normalizer (T0 : Set H) ⊓ I) =
      Nat.card T0 * Nat.card B₀' := by
    rw [hT0, normalizer_map_inf_range Φ hΦ U, Subgroup.card_map_of_injective hΦ, hcardP,
      Subgroup.card_map_of_injective hΦ, hB₀', Subgroup.card_map_of_injective hΦ]
  have hSk : OutSkel I T0 B₀' := ⟨hSylI, hB₀I, hB₀N, hodd₀, hC, hcard⟩
  have hZne : ∃ x ∈ centerOf T0, x ≠ 1 := by
    obtain ⟨x, hx, -, -, hx1, -, -⟩ := hD.Z_big
    exact ⟨Φ x, by rw [hcenT]; exact Subgroup.mem_map_of_mem Φ hx,
      fun h => hx1 (hΦ (by rw [h, map_one]))⟩
  have hZtrans : ∀ x ∈ centerOf T0, x ≠ 1 → ∀ y ∈ centerOf T0, y ≠ 1 →
      ∃ c ∈ B₀', c * x * c⁻¹ = y := by
    intro x hx hx1 y hy hy1
    rw [hcenT] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy1' : y' ≠ 1 := fun h => hy1 (by rw [h, map_one])
    obtain ⟨b, hb, hbxy⟩ := hD.trans x' hx' hx1' y' hy' hy1'
    exact ⟨Φ b, Subgroup.mem_map_of_mem Φ hb, by rw [← map_mul, ← map_inv, ← map_mul, hbxy]⟩
  have hq2 := hO.two_le
  have hout : ∀ b ∈ Subgroup.normalizer (T0 : Set H), (∃ k : ℕ, orderOf b = 2 ^ k) → b ∉ I →
      ¬ ∀ z ∈ centerOf T0, b * z = z * b := by
    intro b hb hk hbI hcentr
    have h3 := (hO.bound b hb hk hbI).2.2 (centerOf T0) hcenT.le hcentr
    rw [hcardZ] at h3
    nlinarith
  have hpc : pCoreOf 2 (N₁ ⊓ N₂) ≤ T0 := by
    rw [hN_eq]; exact hSk.pCore_le rfl hZtrans hZne hout
  have hS_eq : T0 = pCoreOf 2 (N₁ ⊓ N₂) :=
    le_antisymm (le_pCoreOf_of_le_normalizer (le_inf hTN₁ hTN₂) hN_eq.le hTp) hpc
  obtain ⟨Tt, hTt, -⟩ := A4.exists_isSylowTwoOf_ge (P := ⊥) (H := Bt T0 B₀') bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  have hTtN : Tt ≤ Subgroup.normalizer (T0 : Set H) := le_normalizer_of_le_Bt hTt.1
  have hTt2 : IsPGroup 2 Tt := hTt.2.1
  have hTtcard : 2 ∣ Nat.card Tt := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hTt2
    by_cases hk0 : k = 0
    · exfalso
      apply hSk.even_of_index heven
      have h1 := Subgroup.relIndex_mul_card Tt (Bt T0 B₀')
      rw [inf_of_le_left hTt.1, hk, hk0, pow_zero, mul_one] at h1
      rw [← h1]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (F7.isSylowTwoOf_odd_relIndex hTt))
    · rw [hk]; exact dvd_pow_self 2 hk0
  have hTtI : Tt ⊓ I = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxT0 : x ∈ T0 :=
      hSk.le_of_pgroup (X := Tt ⊓ I) (inf_le_inf_right I hTtN) hTt2.to_inf_left hx
    exact hSk.disj x hxT0 (hTt.1 hx.1)
  obtain ⟨hcyc, hTtq⟩ := hO.cyc Tt hTtN hTt2 hTtI
  obtain ⟨f', hf'⟩ := exists_prime_orderOf_dvd_card' (G := ↥Tt) 2 hTtcard
  set f : H := (f' : H) with hfdef
  have hfT : f ∈ Tt := f'.2
  have hford : orderOf f = 2 := by rw [hfdef, Subgroup.orderOf_coe]; exact hf'
  have hf2 : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hford, pow_two] at this
  have hf1 : f ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hford
    omega
  have hfI : f ∉ I := by
    intro h
    have : f ∈ Tt ⊓ I := ⟨hfT, h⟩
    rw [hTtI] at this
    exact hf1 (Subgroup.mem_bot.mp this)
  have hfN : f ∈ Subgroup.normalizer (T0 : Set H) := hTtN hfT
  have hfN₁ : f ∈ Subgroup.normalizer (Q₁ : Set H) := (hO.noswap f hfN).1
  have hfN₂ : f ∈ Subgroup.normalizer (Q₂ : Set H) := (hO.noswap f hfN).2
  have hfT0 : f ∉ T0 := fun h => hf1 (hSk.disj f h (hTt.1 hfT))
  have : IsCyclic Tt := hcyc
  have hTc : ∀ x ∈ Tt, x * f = f * x := fun x hx => commute_of_isCyclic hx hfT
  have hTsyl : IsSylowTwoOf (prodSub T0 Tt hTtN) (Subgroup.normalizer (T0 : Set H)) :=
    hSk.sylow_prod hTt
  set T : Subgroup H := prodSub T0 Tt hTtN with hT
  have hT0T : T0 ≤ T := left_le_prodSub hTtN
  have hTtT : Tt ≤ T := right_le_prodSub hTtN
  have hTp' : IsPGroup 2 T := hTsyl.2.1
  have hTM : T ≤ N₁ ⊓ N₂ := by rw [hN_eq]; exact hTsyl.1
  have hTle₁ : T ≤ N₁ := hTM.trans inf_le_left
  have hTtop : IsSylowTwoOf T ⊤ := hSk.isSylow_top hTsyl hT0T
  have hTsyl₁ : IsSylowTwoOf T N₁ := F7.isSylowTwoOf_mono_right hTtop hTle₁ le_top
  have hcomm_Tt : ∀ x ∈ Tt, ∀ y ∈ Tt, x * y = y * x := fun x hx y hy => commute_of_isCyclic hx hy
  have hT_comm : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ T0 := fun x hx y hy =>
    prodSub_commutator_mem hTtN hcomm_Tt hx hy
  have hcentH : ∀ x ∈ centerOf T0, x ≠ 1 →
      Subgroup.centralizer ({x} : Set H) ≤ Subgroup.normalizer (T0 : Set H) := by
    intro x hx hx1
    rw [hcenT] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hUC : U ≤ Subgroup.centralizer ({x'} : Set P) := fun u hu => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mem_centerOf_iff.mp hx').2 u hu
    have hcP : pCoreOf 2 (Subgroup.centralizer ({x'} : Set P)) = U := by
      apply le_antisymm
      · exact F7.isSylowTwoOf_pCoreOf_le (F7.isSylowTwoOf_mono_right hD.borel.sylow hUC le_top)
      · exact le_pCoreOf_of_le_normalizer hUC (hD.cent x' hx' hx1') hUp
    exact centralizer_le_normalizer_of_pCoreOf Φ hΦ x' hcP
  have hcov : ∀ (R : Subgroup P) (N' : Subgroup H), N' = Subgroup.normalizer
      ((R.map Φ : Subgroup H) : Set H) →
      (∀ x ∈ R, x ≠ 1 → ∃ m ∈ Subgroup.normalizer (R : Set P), m * x * m⁻¹ ∈ centerOf U) →
      ∀ x ∈ R.map Φ, x ≠ 1 → ∃ m ∈ N', m * x * m⁻¹ ∈ centerOf T0 := by
    intro R N' hN' hcv x hx hx1
    obtain ⟨x', hx', rfl⟩ := hx
    have hx1' : x' ≠ 1 := fun h => hx1 (by rw [h, map_one])
    obtain ⟨m, hm, hmx⟩ := hcv x' hx' hx1'
    refine ⟨Φ m, by rw [hN']; exact map_mem_normalizer_map Φ hm, ?_⟩
    rw [hcenT, ← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem Φ hmx
  have hbound := hO.bound f hfN ⟨1, by rw [hford, pow_one]⟩ hfI
  have hZfix : ∀ B : Subgroup H, B ≤ centerOf T0 → (∀ g ∈ B, f * g = g * f) →
      Nat.card B ^ 2 ≤ q := fun B hB hfix => hbound.2.2 B (hcenT ▸ hB) hfix
  have hcardQ₁ : Nat.card Q₁ = q ^ 2 := by
    rw [hQ₁, Subgroup.card_map_of_injective hΦ]; exact hO.card_R₁
  have hcardQ₂ : Nat.card Q₂ = q ^ 2 := by rw [← hF.card_eq]; exact hcardQ₁
  obtain ⟨a, haQ, hfa, haZ⟩ := exists_fixed_not_mem
    (fun x hx y hy => F7.isElemAbelian_comm hF.Q₁_ea hx hy)
    (fun x hx => by rw [← pow_two]; exact F7.isElemAbelian_pow_eq_one hF.Q₁_ea hx) hf2
    (fun v hv => (Subgroup.mem_normalizer_iff.mp hfN₁ v).mp hv) hcardQ₁ hq2 hZfix
  obtain ⟨b, hbQ, hfb, hbZ⟩ := exists_fixed_not_mem
    (fun x hx y hy => F7.isElemAbelian_comm hF.Q₂_ea hx hy)
    (fun x hx => by rw [← pow_two]; exact F7.isElemAbelian_pow_eq_one hF.Q₂_ea hx) hf2
    (fun v hv => (Subgroup.mem_normalizer_iff.mp hfN₂ v).mp hv) hcardQ₂ hq2 hZfix
  obtain ⟨hTfSyl, hcardC⟩ := hSk.sylow_cent hTt hfT hTc
  set C : Subgroup H := Subgroup.centralizer ({f} : Set H) with hCdef
  set Ct : Subgroup H := T ⊓ C with hCt
  set L : Subgroup H := T0 ⊓ C with hL
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hfa.symm
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hfb.symm
  have haT0 : a ∈ T0 := hF.Q₁_le haQ
  have hbT0 : b ∈ T0 := hF.Q₂_le hbQ
  have haCt : a ∈ Ct := ⟨hT0T haT0, haC⟩
  have hbCt : b ∈ Ct := ⟨hT0T hbT0, hbC⟩
  have hCtp : IsPGroup 2 Ct := hTp'.to_inf_left
  have hnoncomm : a * b ≠ b * a := by
    intro hab
    have hbQ₁ : b ∈ Q₁ := hF.cent₁ a haQ haZ b hbT0 hab.symm
    exact hbZ (by rw [← hF.inter]; exact ⟨hbQ₁, hbQ⟩)
  have hcommT0 : ∀ z ∈ T0, z * a = a * z → z * b = b * z → z ∈ centerOf T0 := by
    intro z hz hza hzb
    have hzQ₁ : z ∈ Q₁ := hF.cent₁ a haQ haZ z hz hza
    have hzQ₂ : z ∈ Q₂ := hF.cent₂ b hbQ hbZ z hz hzb
    rw [← hF.inter]
    exact ⟨hzQ₁, hzQ₂⟩
  have hcomm_le : ⁅Ct, Ct⁆ ≤ T0 :=
    Subgroup.commutator_le.mpr (fun x hx y hy => hT_comm x hx.1 y hy.1)
  have hZf_le : centerOf Ct ⊓ ⁅Ct, Ct⁆ ≤ centerOf T0 := by
    rintro z ⟨hzc, hzcomm⟩
    have hz := mem_centerOf_iff.mp hzc
    exact hcommT0 z (hcomm_le hzcomm) (hz.2 a haCt).symm (hz.2 b hbCt).symm
  have hZn : ∀ r ∈ Ct, ∀ z ∈ ⁅Ct, Ct⁆, r * z * r⁻¹ ∈ ⁅Ct, Ct⁆ := by
    intro r hr z hz
    have h1 : conjSub r ⁅Ct, Ct⁆ = ⁅Ct, Ct⁆ := by
      rw [← conjSub_commutator, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hr)]
    rw [← h1]
    exact mul_mem_conjSub hz
  have hZf_ne : centerOf Ct ⊓ ⁅Ct, Ct⁆ ≠ ⊥ := by
    have hcomm1 : ⁅a, b⁆ ≠ 1 := by
      intro h
      apply hnoncomm
      rw [commutatorElement_def] at h
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h, one_mul]
    have hne : ∃ z ∈ ⁅Ct, Ct⁆, z ≠ 1 :=
      ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator haCt hbCt, hcomm1⟩
    obtain ⟨z, hzcomm, hz1, hzc⟩ := exists_central_of_normalized hCtp
      (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => Ct.mul_mem (Ct.mul_mem (Ct.mul_mem hg₁ hg₂)
        (Ct.inv_mem hg₁)) (Ct.inv_mem hg₂)) hZn hne
    intro h
    have hmem : z ∈ centerOf Ct ⊓ ⁅Ct, Ct⁆ := by
      refine ⟨mem_centerOf_iff.mpr ⟨?_, fun s hs => hzc s hs⟩, hzcomm⟩
      exact Subgroup.commutator_le.mpr (fun g₁ hg₁ g₂ hg₂ => Ct.mul_mem (Ct.mul_mem
        (Ct.mul_mem hg₁ hg₂) (Ct.inv_mem hg₁)) (Ct.inv_mem hg₂)) hzcomm
    rw [h] at hmem
    exact hz1 (Subgroup.mem_bot.mp hmem)
  have hrel : Q₁.relIndex T0 = q := by
    have hQ₂N : Q₂ ≤ Subgroup.normalizer (Q₁ : Set H) := by
      rw [← h₁]; exact hF.Q₂_le.trans hTN₁
    have h1 := A4.relIndex_sup_eq_of_le_normalizer' hQ₂N
    rw [sup_comm, ← hTsup] at h1
    have h2 := Subgroup.relIndex_mul_card Q₁ Q₂
    rw [hF.inter, hcardZ, hcardQ₂] at h2
    rw [h1]
    have hpos : 0 < q := by omega
    have : Q₁.relIndex Q₂ * q = q * q := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hcardT0 : Nat.card T0 = q ^ 3 := by
    have h := Subgroup.relIndex_mul_card Q₁ T0
    rw [inf_of_le_left hF.Q₁_le, hrel, hcardQ₁] at h
    rw [← h]; ring
  have hLq : Nat.card L ≤ q ^ 2 := by
    have h1 := Subgroup.relIndex_mul_card Q₁ L
    have h2 : Nat.card ↥(Q₁ ⊓ L) ≤ q := by
      refine hbound.1 (Q₁ ⊓ L) inf_le_left fun g hg => ?_
      have hg' : g ∈ C := hg.2.2
      exact (Subgroup.mem_centralizer_singleton_iff.mp hg').symm
    have h3 : Q₁.relIndex L ≤ q := by
      rw [← hrel]
      exact Subgroup.relIndex_le_of_le_right inf_le_left
        (by show (Q₁.subgroupOf T0).index ≠ 0; exact Subgroup.index_ne_zero_of_finite)
    rw [← h1, sq]
    exact Nat.mul_le_mul h3 h2
  have hTf_lt : Nat.card Ct < Nat.card T0 := by
    rw [hcardC, hcardT0]
    calc Nat.card L * Nat.card Tt ≤ q ^ 2 * Nat.card Tt := Nat.mul_le_mul_right _ hLq
      _ < q ^ 2 * q := Nat.mul_lt_mul_of_pos_left hTtq (by positivity)
      _ = q ^ 3 := by ring
  exact ⟨{
    S := T0
    T := T
    B := B₀'
    f := f
    S_eq := hS_eq
    S_le_T := hT0T
    T_le := hTM
    T_pgroup := hTp'
    T_index := F7.isSylowTwoOf_odd_relIndex hTsyl₁
    B_le := by rw [hN_eq]; exact hB₀N
    trans := hZtrans
    cent := fun x hx hx1 y _ hy => by
      have hyN : y ∈ Subgroup.normalizer (T0 : Set H) :=
        hcentH x hx hx1 (Subgroup.mem_centralizer_singleton_iff.mpr hy)
      rw [h₂]
      exact (hO.noswap y hyN).2
    ZT := by
      intro w hw
      obtain ⟨hwT, hwc⟩ := mem_centerOf_iff.mp hw
      by_cases hwI : w ∈ I
      · have hwT0 : w ∈ T0 := hSk.le_of_pgroup (X := T ⊓ I) (inf_le_inf_right I hTsyl.1)
          hTp'.to_inf_left ⟨hwT, hwI⟩
        exact mem_centerOf_iff.mpr ⟨hwT0, fun s hs => hwc s (hT0T hs)⟩
      · exfalso
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTp') ⟨w, hwT⟩
        have hwN : w ∈ Subgroup.normalizer (T0 : Set H) := hTsyl.1 hwT
        have h1 := (hO.bound w hwN ⟨k, by rw [← Subgroup.orderOf_mk w hwT]; exact hk⟩ hwI).1 Q₁
          le_rfl (fun g hg => (hwc g (hT0T (hF.Q₁_le hg))).symm)
        rw [hcardQ₁] at h1
        nlinarith
    invS := by
      intro x hx hx2 hx1
      have hx2' : x ^ 2 = 1 := by rw [pow_two]; exact hx2
      rcases hF.inv x hx hx2' hx1 with h | h
      · obtain ⟨m, hm, hmx⟩ := hcov R₁ N₁ h₁ hD.half₁.cov x h hx1
        exact ⟨m, Or.inl hm, hmx⟩
      · obtain ⟨m, hm, hmx⟩ := hcov R₂ N₂ h₂ hD.half₂.cov x h hx1
        exact ⟨m, Or.inr hm, hmx⟩
    f_mem := hTtT hfT
    f_not := hfT0
    f_sq := hf2
    T_comm := hT_comm
    T_cyc := fun x hx y hy hxS hyS hx2 hy2 =>
      prodSub_cyc_mem hTtN (fun x hx hxT => hSk.disj x hx (hTt.1 hxT))
        (fun s hs t ht hs2 ht2 hs1 ht1 => eq_of_sq_eq_one_of_isCyclic hs ht hs2 ht2 hs1 ht1)
        hx hy hxS hyS hx2 hy2
    Tf_sylow := by rw [hN_eq]; exact hTfSyl
    Zf_ne := hZf_ne
    Zf_le := hZf_le
    Tf_lt := hTf_lt }⟩

end Lift

end CFSG.Quasithin.H13.F431.L3
