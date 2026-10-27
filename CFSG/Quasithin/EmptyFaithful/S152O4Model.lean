module

public import CFSG.Quasithin.EmptyFaithful.S153Ofour
public import CFSG.Quasithin.Background.D2Tools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution
public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S152O

theorem sl2_cube_aux : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a ∧ (a * b) ^ 3 = 1 := by
  decide +kernel

section Natural

variable {W : Type*} [CommGroup W]

theorem cube_aux {L : Subgroup (MulAut W)} {U : Subgroup W} (hN : ActsAsNaturalL2 L U)
    {l l' : MulAut W} (hl : l ∈ L) (hl' : l' ∈ L) (h3 : l ^ 3 = 1) (h3' : l' ^ 3 = 1) :
    l * l' = l' * l ∧ (l * l') ^ 3 = 1 := by
  obtain ⟨e, -, -⟩ := hN
  have h1 : (e ⟨l, hl⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨l, hl⟩ : L) ^ 3 = 1 := Subtype.ext h3
    rw [this, map_one]
  have h2 : (e ⟨l', hl'⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨l', hl'⟩ : L) ^ 3 = 1 := Subtype.ext h3'
    rw [this, map_one]
  obtain ⟨hc, hp⟩ := sl2_cube_aux _ _ h1 h2
  constructor
  · have : (⟨l, hl⟩ : L) * ⟨l', hl'⟩ = ⟨l', hl'⟩ * ⟨l, hl⟩ := e.injective (by rw [map_mul, map_mul, hc])
    exact congrArg Subtype.val this
  · have : ((⟨l, hl⟩ : L) * ⟨l', hl'⟩) ^ 3 = 1 := e.injective (by rw [map_pow, map_mul, hp, map_one])
    exact congrArg Subtype.val this

end Natural

section General

variable {G : Type*} [Group G]

theorem le_oddCoreIn_of_normalizes {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) : K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

theorem inverts_of_commutator_eq {E B : Subgroup G} {b : G} (hb2 : b ^ 2 = 1)
    (hbE : b ∈ Subgroup.normalizer (E : Set G)) (hBb : ∀ x ∈ B, x = 1 ∨ x = b)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcomm : ⁅E, B⁆ = E) :
    ∀ e ∈ E, b * e * b⁻¹ = e⁻¹ := by
  have hbinv : b⁻¹ = b := by
    have h1 : b * b = 1 := by rw [← sq]; exact hb2
    exact inv_eq_of_mul_eq_one_right h1
  let I : Subgroup G :=
    { carrier := {e | e ∈ E ∧ b * e * b⁻¹ = e⁻¹}
      one_mem' := ⟨E.one_mem, by simp⟩
      mul_mem' := by
        rintro a c ⟨ha, ha'⟩ ⟨hc, hc'⟩
        refine ⟨E.mul_mem ha hc, ?_⟩
        have e1 : b * (a * c) * b⁻¹ = (b * a * b⁻¹) * (b * c * b⁻¹) := by group
        rw [e1, ha', hc', mul_inv_rev, hab _ (E.inv_mem ha) _ (E.inv_mem hc)]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨E.inv_mem ha, ?_⟩
        have e1 : b * a⁻¹ * b⁻¹ = (b * a * b⁻¹)⁻¹ := by group
        rw [e1, ha'] }
  have hle : ⁅E, B⁆ ≤ I := by
    rw [Subgroup.commutator_le]
    intro e he x hx
    have hxE : x * e⁻¹ * x⁻¹ ∈ E := by
      rcases hBb x hx with rfl | rfl
      · simpa using E.inv_mem he
      · exact (Subgroup.mem_normalizer_iff.mp hbE e⁻¹).mp (E.inv_mem he)
    refine ⟨?_, ?_⟩
    · have : ⁅e, x⁆ = e * (x * e⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact E.mul_mem he hxE
    · rcases hBb x hx with rfl | rfl
      · simp
      · simp only [commutatorElement_def]
        rw [hbinv]
        have e2 : x * (e * x * e⁻¹ * x) * x = x * e * x * e⁻¹ * (x * x) := by group
        have e3 : x * x = 1 := by rw [← sq]; exact hb2
        have e4 : (e * x * e⁻¹ * x)⁻¹ = x⁻¹ * e * x⁻¹ * e⁻¹ := by group
        rw [e2, e3, e4, hbinv]
        group
  rw [hcomm] at hle
  exact fun e he => (hle he).2

theorem eq_of_card_eq_two {Γ : Type*} [Group Γ] (h : Nat.card Γ = 2) {a b : Γ} (ha : a ≠ 1)
    (hb : b ≠ 1) : a = b := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : Γ)).mp h
  rw [huniq a ha, huniq b hb]

end General

section Struct

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem odd_of_pow_three {x : MulAut W} (h : x ^ 3 = 1) : Odd (orderOf x) :=
  Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h)

theorem decomp_cube (hS : OfourStruct X L₁ L₂ t) {x : MulAut W} (hx : x ∈ X) (h3 : x ^ 3 = 1) :
    ∃ l₁ ∈ L₁, ∃ l₂ ∈ L₂, x = l₁ * l₂ ∧ l₁ ^ 3 = 1 ∧ l₂ ^ 3 = 1 :=
  hS.odd_decomp (hS.odd_mem_sup hx (odd_of_pow_three h3)) (odd_of_pow_three h3)

theorem exists_cubeSub (hS : OfourStruct X L₁ L₂ t) :
    ∃ P : Subgroup (MulAut W), ∀ x, x ∈ P ↔ x ∈ X ∧ x ^ 3 = 1 := by
  refine ⟨{ carrier := {x | x ∈ X ∧ x ^ 3 = 1}
            one_mem' := ⟨X.one_mem, one_pow 3⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hxX, hx3⟩ ⟨hyX, hy3⟩
    refine ⟨X.mul_mem hxX hyX, ?_⟩
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl, hl₁3, hl₂3⟩ := decomp_cube hS hxX hx3
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl, hm₁3, hm₂3⟩ := decomp_cube hS hyX hy3
    have hc : m₁ * l₂ = l₂ * m₁ := hS.comm m₁ hm₁ l₂ hl₂
    have e : l₁ * l₂ * (m₁ * m₂) = (l₁ * m₁) * (l₂ * m₂) := by
      calc l₁ * l₂ * (m₁ * m₂) = l₁ * (l₂ * m₁) * m₂ := by simp only [mul_assoc]
        _ = l₁ * (m₁ * l₂) * m₂ := by rw [hc]
        _ = (l₁ * m₁) * (l₂ * m₂) := by simp only [mul_assoc]
    rw [e, Commute.mul_pow (hS.comm _ (L₁.mul_mem hl₁ hm₁) _ (L₂.mul_mem hl₂ hm₂)),
      (cube_aux hS.nat₁ hl₁ hm₁ hl₁3 hm₁3).2, (cube_aux hS.nat₂ hl₂ hm₂ hl₂3 hm₂3).2, one_mul]
  · rintro x ⟨hxX, hx3⟩
    exact ⟨X.inv_mem hxX, by rw [inv_pow, hx3, inv_one]⟩

variable {P : Subgroup (MulAut W)}

theorem cubeSub_conj (hP : ∀ x, x ∈ P ↔ x ∈ X ∧ x ^ 3 = 1) {g : MulAut W} (hg : g ∈ X)
    {x : MulAut W} (hx : x ∈ P) : g * x * g⁻¹ ∈ P := by
  obtain ⟨hxX, hx3⟩ := (hP x).mp hx
  refine (hP _).mpr ⟨X.mul_mem (X.mul_mem hg hxX) (X.inv_mem hg), ?_⟩
  rw [conj_pow, hx3]
  simp

theorem normalizes_cubeSub (hP : ∀ x, x ∈ P ↔ x ∈ X ∧ x ^ 3 = 1) {Y : Subgroup (MulAut W)}
    (hY : Y ≤ X) : Y ≤ Subgroup.normalizer (P : Set (MulAut W)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => cubeSub_conj hP (hY hg) hx, fun hx => ?_⟩
  have := cubeSub_conj hP (X.inv_mem (hY hg)) hx
  simpa [mul_assoc] using this

theorem cubeSub_comm (hS : OfourStruct X L₁ L₂ t) (hP : ∀ x, x ∈ P ↔ x ∈ X ∧ x ^ 3 = 1)
    {x y : MulAut W} (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  obtain ⟨hxX, hx3⟩ := (hP x).mp hx
  obtain ⟨hyX, hy3⟩ := (hP y).mp hy
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl, hl₁3, hl₂3⟩ := decomp_cube hS hxX hx3
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl, hm₁3, hm₂3⟩ := decomp_cube hS hyX hy3
  have h1 := (cube_aux hS.nat₁ hl₁ hm₁ hl₁3 hm₁3).1
  have h2 := (cube_aux hS.nat₂ hl₂ hm₂ hl₂3 hm₂3).1
  have hc : m₁ * l₂ = l₂ * m₁ := hS.comm m₁ hm₁ l₂ hl₂
  have hc' : l₁ * m₂ = m₂ * l₁ := hS.comm l₁ hl₁ m₂ hm₂
  calc l₁ * l₂ * (m₁ * m₂) = l₁ * (l₂ * m₁) * m₂ := by simp only [mul_assoc]
    _ = l₁ * (m₁ * l₂) * m₂ := by rw [hc]
    _ = (l₁ * m₁) * (l₂ * m₂) := by simp only [mul_assoc]
    _ = (m₁ * l₁) * (m₂ * l₂) := by rw [h1, h2]
    _ = m₁ * (l₁ * m₂) * l₂ := by simp only [mul_assoc]
    _ = m₁ * (m₂ * l₁) * l₂ := by rw [hc']
    _ = m₁ * m₂ * (l₁ * l₂) := by simp only [mul_assoc]

theorem odd_card_cubeSub [Finite W] (hP : ∀ x, x ∈ P ↔ x ∈ X ∧ x ^ 3 = 1) :
    Odd (Nat.card P) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card P := by
    rcases Nat.even_or_odd (Nat.card P) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 h2
  have hx3 : (x : MulAut W) ^ 3 = 1 := ((hP _).mp x.2).2
  have h1 : orderOf (x : MulAut W) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rw [Subgroup.orderOf_coe, hx] at h1
  omega

theorem cubeSub_le_of_rank [Finite W] {X' : Subgroup (MulAut W)} (hexp : ∀ w : W, w ^ 2 = 1)
    (hP : ∀ x, x ∈ P ↔ x ∈ X ∧ x ^ 3 = 1)
    (hX' : ∀ g, g ∈ X' ↔ g ∈ X ∧ Even (rk (commV (Subgroup.zpowers g)))) : P ≤ X' := by
  intro x hx
  obtain ⟨hxX, hx3⟩ := (hP x).mp hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact X'.one_mem
  · refine (hX' x).mpr ⟨hxX, ?_⟩
    have hord : orderOf x = 3 := by
      have hdvd := orderOf_dvd_of_pow_eq_one hx3
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
    exact (commV_card_three hexp hcard).2.2.2

theorem oddCoreIn_eq [Finite W] (hS : OfourStruct X L₁ L₂ t) {X' : Subgroup (MulAut W)}
    (hexp : ∀ w : W, w ^ 2 = 1) (hP : ∀ x, x ∈ P ↔ x ∈ X ∧ x ^ 3 = 1)
    (hX' : ∀ g, g ∈ X' ↔ g ∈ X ∧ Even (rk (commV (Subgroup.zpowers g)))) :
    oddCoreIn X' = P := by
  apply le_antisymm
  · intro x hx
    have hxX' : x ∈ X' := oddCoreIn_le X' hx
    have hxX : x ∈ X := ((hX' x).mp hxX').1
    have hodd : Odd (orderOf x) :=
      (odd_card_oddCoreIn X').of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn X') hx)
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl, hl₁3, hl₂3⟩ := hS.odd_decomp (hS.odd_mem_sup hxX hodd) hodd
    refine (hP _).mpr ⟨hxX, ?_⟩
    rw [Commute.mul_pow (hS.comm _ hl₁ _ hl₂), hl₁3, hl₂3, one_mul]
  · exact le_oddCoreIn_of_normalizes (cubeSub_le_of_rank hexp hP hX')
      (normalizes_cubeSub hP (fun g hg => ((hX' g).mp hg).1)) (odd_card_cubeSub hP)

end Struct

section Main

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem key_fixed (hS : OfourStruct X L₁ L₂ t) {B₀ : Subgroup (MulAut W)} {b l₁ l₂ c : MulAut W}
    (hl₁ : l₁ ∈ L₁) (hl₂ : l₂ ∈ L₂) (hbl : l₁ * l₂ = b) (hl₁1 : l₁ ≠ 1) (hc : c ∈ L₂)
    (hbB : b ∈ B₀) : ∃ u ∈ commV B₀, u ≠ 1 ∧ c u = u := by
  obtain ⟨w, hw, hlw⟩ : ∃ w ∈ commV L₁, l₁ w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hl₁1 (eq_one_of_forall_apply_eq hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) hl₁
      hcon)
  have hl₁w : l₁ w ∈ commV L₁ := commV_stable L₁ hl₁ hw
  have hu : l₁ w * w⁻¹ ∈ commV L₁ := (commV L₁).mul_mem hl₁w ((commV L₁).inv_mem hw)
  refine ⟨l₁ w * w⁻¹, ?_, ?_, hS.L₂_fix₁ hc hu⟩
  · have hbw : b w = l₁ w := by
      rw [← hbl, MulAut.mul_apply, hS.L₂_fix₁ hl₂ hw]
    rw [← hbw]
    exact Subgroup.subset_closure ⟨b, hbB, w, rfl⟩
  · intro h1
    exact hlw (mul_inv_eq_one.mp h1)

theorem exists_fixed_vector_of_ofourStruct [Finite W] (hS : OfourStruct X L₁ L₂ t)
    (hexp : ∀ w : W, w ^ 2 = 1) {X' B₀ : Subgroup (MulAut W)}
    (hX' : ∀ g, g ∈ X' ↔ g ∈ X ∧ Even (rk (commV (Subgroup.zpowers g))))
    (hB₀le : B₀ ≤ X') (hB₀ : Nat.card B₀ = 2) (hO : oddCoreIn X' = ⁅oddCoreIn X', B₀⁆) :
    ∃ u ∈ commV B₀, u ≠ 1 ∧ ∃ c ∈ X', c ≠ 1 ∧ c ^ 3 = 1 ∧ c u = u := by
  obtain ⟨P, hP⟩ := exists_cubeSub hS
  have hPX' : P ≤ X' := cubeSub_le_of_rank hexp hP hX'
  have hOP : oddCoreIn X' = P := oddCoreIn_eq hS hexp hP hX'
  have hB'ne : B₀ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hB₀
    omega
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B₀, b ≠ 1 := by
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB'ne
    exact ⟨b, b.2, fun h => hb1 (Subtype.ext h)⟩
  have hb2 : b ^ 2 = 1 := by
    have : orderOf (⟨b, hbB⟩ : B₀) ∣ 2 := hB₀ ▸ orderOf_dvd_natCard _
    simpa using congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp this)
  have hBb : ∀ x ∈ B₀, x = 1 ∨ x = b := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have := eq_of_card_eq_two hB₀ (a := (⟨x, hx⟩ : B₀)) (b := ⟨b, hbB⟩)
        (fun h => hx1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  have hbX' : b ∈ X' := hB₀le hbB
  have hbX : b ∈ X := ((hX' b).mp hbX').1
  have hnormP : b ∈ Subgroup.normalizer (P : Set (MulAut W)) :=
    normalizes_cubeSub hP (fun g hg => ((hX' g).mp hg).1) hbX'
  have hinv : ∀ e ∈ P, b * e * b⁻¹ = e⁻¹ := by
    refine inverts_of_commutator_eq hb2 hnormP hBb (fun x hx y hy => cubeSub_comm hS hP hx hy) ?_
    rw [hOP] at hO
    exact hO.symm
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a₁, ha₁⟩ := exists_prime_orderOf_dvd_card' (G := L₁) 3 (by rw [hS.card_L₁]; norm_num)
  obtain ⟨a₂, ha₂⟩ := exists_prime_orderOf_dvd_card' (G := L₂) 3 (by rw [hS.card_L₂]; norm_num)
  have ha₁3 : (a₁ : MulAut W) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (a₁ : MulAut W)
    rwa [Subgroup.orderOf_coe, ha₁] at this
  have ha₂3 : (a₂ : MulAut W) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (a₂ : MulAut W)
    rwa [Subgroup.orderOf_coe, ha₂] at this
  have ha₁1 : (a₁ : MulAut W) ≠ 1 := by
    intro h
    have h1 : orderOf (a₁ : MulAut W) = 1 := by rw [h]; exact orderOf_one
    rw [Subgroup.orderOf_coe, ha₁] at h1
    omega
  have ha₂1 : (a₂ : MulAut W) ≠ 1 := by
    intro h
    have h1 : orderOf (a₂ : MulAut W) = 1 := by rw [h]; exact orderOf_one
    rw [Subgroup.orderOf_coe, ha₂] at h1
    omega
  have ha₁P : (a₁ : MulAut W) ∈ P := (hP _).mpr ⟨hS.L₁_le a₁.2, ha₁3⟩
  have ha₂P : (a₂ : MulAut W) ∈ P := (hP _).mpr ⟨hS.L₂_le a₂.2, ha₂3⟩
  have hbN : b ∈ L₁ ⊔ L₂ := by
    rcases hS.perm b hbX with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (hS.mem_sup_iff hbX).mpr fun u hu => OfourStruct.commV_apply_mem b L₁ L₁ h1 hu
    · exfalso
      have hconj : b * (a₁ : MulAut W) * b⁻¹ = (a₁ : MulAut W)⁻¹ := hinv _ ha₁P
      have hmem : b * (a₁ : MulAut W) * b⁻¹ ∈ L₂ := by
        have : b * (a₁ : MulAut W) * b⁻¹ ∈ B1.conjAut b L₁ := by
          rw [B1.mem_conjAut]
          simp [mul_assoc]
        rwa [h1] at this
      rw [hconj] at hmem
      have : (a₁ : MulAut W)⁻¹ ∈ L₁ ⊓ L₂ := ⟨L₁.inv_mem a₁.2, hmem⟩
      rw [hS.Linf, Subgroup.mem_bot, inv_eq_one] at this
      exact ha₁1 this
  obtain ⟨l₁, hl₁, l₂, hl₂, hbl⟩ := exists_mul_of_mem_sup_of_commute hS.comm hbN
  by_cases hl₁1 : l₁ = 1
  · have hl₂1 : l₂ ≠ 1 := by
      intro h
      apply hb1
      rw [← hbl, hl₁1, h, mul_one]
    have hbl' : l₂ * l₁ = b := by
      rw [← hbl]
      exact (hS.comm l₁ hl₁ l₂ hl₂).symm
    obtain ⟨u, hu, hu1, hcu⟩ := key_fixed hS.symm hl₂ hl₁ hbl' hl₂1 a₁.2 hbB
    exact ⟨u, hu, hu1, a₁, hPX' ha₁P, ha₁1, ha₁3, hcu⟩
  · obtain ⟨u, hu, hu1, hcu⟩ := key_fixed hS hl₁ hl₂ hbl hl₁1 a₂.2 hbB
    exact ⟨u, hu, hu1, a₂, hPX' ha₂P, ha₂1, ha₂3, hcu⟩

theorem exists_fixed_vector_of_isOmegaFourPlus [Finite W] (hexp : ∀ w : W, w * w = 1)
    {X' B₀ : Subgroup (MulAut W)} (hΩ : IsOmegaFourPlus X') (hB₀le : B₀ ≤ X')
    (hB₀ : Nat.card B₀ = 2) (hO : oddCoreIn X' = ⁅oddCoreIn X', B₀⁆) :
    ∃ u ∈ commV B₀, u ≠ 1 ∧ ∃ c ∈ X', c ≠ 1 ∧ c ^ 3 = 1 ∧ c u = u := by
  obtain ⟨hcard, q, hq, hn, hp, hmem⟩ := hΩ
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq hn hp
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  exact exists_fixed_vector_of_ofourStruct hS hW2 hmem hB₀le hB₀ hO

end Main

end S152O

end CFSG.Quasithin
