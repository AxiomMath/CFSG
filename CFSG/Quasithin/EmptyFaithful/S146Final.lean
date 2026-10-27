module

public import CFSG.Quasithin.EmptyFaithful.S146Inputs
public import CFSG.Quasithin.EmptyFaithful.S1421Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def FinalData146 (T M : Subgroup G) : Prop :=
  ∃ (H : Subgroup G) (u : G) (H₂ : Subgroup G),
    IsHTM T M H ∧ IsInvU T M H u ∧ IsI T M u (Subgroup.centralizer ({u} : Set G)) ∧
    4 < (pCoreOf 2 H).relIndex T ∧
    4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)) ∧
    tZero T u ≤ H₂ ∧
    H₂ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ∧
    Nonempty (OTwoQuot H₂ ≃* Equiv.Perm (Fin 3)) ∧ ¬ H₂ ≤ M ∧ HasTwoNoncentralChiefFactors H₂ ∧
    Nat.card (conjClosure (VZ T M) (oTwoUpper H₂)) = 2 ^ 4

theorem exists_isIStar_choice {T M : Subgroup G} {u : G}
    (hC : IsI T M u (Subgroup.centralizer ({u} : Set G))) :
    ∃ I, IsIStar T M u I ∧ (T ⊓ I = tU T u → I ≤ Subgroup.centralizer ({u} : Set G)) := by
  classical
  obtain ⟨J, hJ, hJmax⟩ := Set.exists_max_image {J : Subgroup G | IsI T M u J}
    (fun J => Nat.card ↥(T ⊓ J)) (Set.toFinite _) ⟨_, hC⟩
  have hJstar : IsIStar T M u J := ⟨hJ, fun K hK hlt => by
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := hJmax K hK
    omega⟩
  by_cases hex : ∃ I', IsIStar T M u I' ∧ T ⊓ I' = tU T u
  · obtain ⟨I', hI', hT⟩ := hex
    have hTC : T ⊓ I' ≤ Subgroup.centralizer ({u} : Set G) := by rw [hT]; exact inf_le_right
    obtain ⟨hCstar, -⟩ := hI'.of_le_inf hC hTC
    exact ⟨_, hCstar, fun _ => le_rfl⟩
  · exact ⟨J, hJstar, fun h => absurd ⟨J, hJstar, h⟩ hex⟩

omit [Finite G] in
theorem commute_of_odd_orderOf {Z : Subgroup G} {x u : G} (hZ : Nat.card Z = 2)
    (hxZ : x ∈ Subgroup.centralizer (Z : Set G))
    (hz : x * u * x⁻¹ * u⁻¹ ∈ Z) (hodd : Odd (orderOf x)) : x * u = u * x := by
  set z : G := x * u * x⁻¹ * u⁻¹ with hzdef
  have hz2 : z ^ 2 = 1 := by
    have hdvd := Subgroup.orderOf_dvd_natCard Z hz
    rw [hZ] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.mp hxZ) z hz
  have hxu : x * u * x⁻¹ = z * u := by rw [hzdef]; group
  have key : ∀ k : ℕ, x ^ k * u * (x ^ k)⁻¹ = z ^ k * u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : x ^ (k + 1) * u * (x ^ (k + 1))⁻¹ = x * (x ^ k * u * (x ^ k)⁻¹) * x⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih]
      have hxzk : x * z ^ k = z ^ k * x :=
        (Commute.pow_right (show Commute x z from hzx.symm) k).eq
      calc x * (z ^ k * u) * x⁻¹ = (x * z ^ k) * u * x⁻¹ := by group
        _ = (z ^ k * x) * u * x⁻¹ := by rw [hxzk]
        _ = z ^ k * (x * u * x⁻¹) := by group
        _ = z ^ (k + 1) * u := by rw [hxu, pow_succ]; group
  have h1 := key (orderOf x)
  rw [pow_orderOf_eq_one] at h1
  simp only [inv_one, mul_one, one_mul] at h1
  have hzk : z ^ orderOf x = 1 := by
    have : z ^ orderOf x * u = 1 * u := by rw [← h1]; simp
    simpa using this
  have hz1 : z = 1 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul] at hzk
    exact hzk
  have : x * u * x⁻¹ * u⁻¹ = 1 := hz1
  calc x * u = (x * u * x⁻¹ * u⁻¹) * (u * x) := by group
    _ = u * x := by rw [this, one_mul]

omit [Finite G] in
theorem conjClosure_sup_eq_of_normalizes {V A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hBV : B ≤ Subgroup.normalizer (V : Set G)) :
    conjClosure V (A ⊔ B) = conjClosure V A := by
  refine le_antisymm (conjClosure_le fun g hg v hv => ?_) (conjClosure_mono le_rfl le_sup_left)
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right B A hBA
  have hg' : g ∈ ((B ⊔ A : Subgroup G) : Set G) := by rw [sup_comm]; exact hg
  rw [hmul] at hg'
  obtain ⟨b, hb, a, ha, rfl⟩ := hg'
  have hbV : ∀ z ∈ V, b * z * b⁻¹ ∈ V := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hBV hb) z).mp hz
  have hbA : ∀ h ∈ A, b * h * b⁻¹ ∈ A := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp (hBA hb) h).mp hh
  have h1 : a * v * a⁻¹ ∈ conjClosure V A := mem_conjClosure ha hv
  have h2 := conj_mem_conjClosure hbV hbA h1
  have e : b * a * v * (b * a)⁻¹ = b * (a * v * a⁻¹) * b⁻¹ := by group
  rw [e]
  exact h2

omit [Finite G] in
theorem sign_eq_one_of_odd_orderOf {g : Equiv.Perm (Fin 3)} (h : Odd (orderOf g)) :
    Equiv.Perm.sign g = 1 := by
  have h1 : (Equiv.Perm.sign g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h2 | h2
  · exact h2
  · rw [h2, Odd.neg_one_pow h] at h1; exact absurd h1 (by decide)

theorem perm3_alt_pow : ∀ g h : Equiv.Perm (Fin 3), Equiv.Perm.sign g = 1 →
    Equiv.Perm.sign h = 1 → h ≠ 1 → ∃ k : Fin 3, h ^ (k : ℕ) = g := by decide

theorem perm3_three_cycle_not_two_group :
    ∃ c : Equiv.Perm (Fin 3), ∀ k : ℕ, c ^ 2 ^ k ≠ 1 := by
  refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, fun k hk => ?_⟩
  have h3 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
  have hne : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ≠ 1 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord := orderOf_eq_prime h3 hne
  have hdvd : orderOf (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  rw [hord] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

open CFSG.LieType.BorelTits in
theorem le_sup_pCoreOf_of_S3 {X L A Tb : Subgroup G} (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hL : oTwoUpper L = L) (hA : oTwoUpper A = A)
    (hAL : A ≤ L) (hS3 : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)))
    (hTb : IsPGroup 2 Tb) (hTbX : Tb ≤ X) (hX : X = (A ⊔ Tb) ⊔ pCoreOf 2 X) :
    L ≤ A ⊔ pCoreOf 2 L := by
  obtain ⟨e⟩ := hS3
  let q : ↥X →* OTwoQuot X := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)
  let ψ : ↥X →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp q
  have hψsurj : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
    intro x
    constructor
    · intro h
      have h1 : q x = 1 := by
        have : e (q x) = e 1 := by simpa [ψ] using h
        exact e.injective this
      exact ⟨x, (QuotientGroup.eq_one_iff x).mp h1, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      subst hyx'
      have h1 : q y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
      simp [ψ, h1]
  have hP : ∀ B : Subgroup G, B ≤ X → oTwoUpper B = B → ∀ x ∈ B,
      ∃ hx : x ∈ X, Equiv.Perm.sign (ψ ⟨x, hx⟩) = 1 := by
    intro B hBX hB x hx
    have hx' : x ∈ oTwoUpper B := by rw [hB]; exact hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      refine ⟨hBX hy.1, sign_eq_one_of_odd_orderOf ?_⟩
      have hdvd : orderOf (ψ ⟨y, hBX hy.1⟩) ∣ orderOf (⟨y, hBX hy.1⟩ : ↥X) := orderOf_map_dvd ψ _
      rw [Subgroup.orderOf_mk] at hdvd
      exact Odd.of_dvd_nat hy.2 hdvd
    | one =>
      refine ⟨X.one_mem, ?_⟩
      have : (⟨1, X.one_mem⟩ : ↥X) = 1 := rfl
      rw [this, map_one, map_one]
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, sx⟩ := ihx
      obtain ⟨hy, sy⟩ := ihy
      refine ⟨X.mul_mem hx hy, ?_⟩
      have : (⟨x * y, X.mul_mem hx hy⟩ : ↥X) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, sx, sy, mul_one]
    | inv x _ ihx =>
      obtain ⟨hx, sx⟩ := ihx
      refine ⟨X.inv_mem hx, ?_⟩
      have : (⟨x⁻¹, X.inv_mem hx⟩ : ↥X) = (⟨x, hx⟩ : ↥X)⁻¹ := rfl
      rw [this, map_inv, map_inv, sx, inv_one]
  have hAX : A ≤ X := hAL.trans hLX
  obtain ⟨a, haA, haψ⟩ : ∃ a ∈ A, ∃ ha : a ∈ X, ψ ⟨a, ha⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc⟩ := perm3_three_cycle_not_two_group
    obtain ⟨x, hx⟩ := hψsurj c
    let φ : Subgroup (Equiv.Perm (Fin 3)) := (Tb.subgroupOf X).map ψ
    let R : Subgroup G := (φ.comap ψ).map X.subtype
    have hAR : A ≤ R := fun a ha => ⟨⟨a, hAX ha⟩, by
      show ψ ⟨a, hAX ha⟩ ∈ φ
      rw [hcon a ha (hAX ha)]; exact φ.one_mem, rfl⟩
    have hTR : Tb ≤ R := fun t ht => ⟨⟨t, hTbX ht⟩, by
      show ψ ⟨t, hTbX ht⟩ ∈ φ
      exact ⟨⟨t, hTbX ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩, rfl⟩
    have hQR : pCoreOf 2 X ≤ R := fun c' hc' => ⟨⟨c', pCoreOf_le 2 X hc'⟩, by
      show ψ ⟨c', pCoreOf_le 2 X hc'⟩ ∈ φ
      rw [(hψker _).mpr hc']; exact φ.one_mem, rfl⟩
    have hXR : X ≤ R := by
      rw [hX]; exact sup_le (sup_le hAR hTR) hQR
    have hxR := hXR x.2
    obtain ⟨x', hx'φ, hx'x⟩ := hxR
    have hx'eq : x' = x := Subtype.ext hx'x
    subst hx'eq
    have hcφ : c ∈ φ := by rw [← hx]; exact hx'φ
    obtain ⟨t, ht, htc⟩ := hcφ
    have hTbp : IsPGroup 2 (Tb.subgroupOf X) :=
      hTb.of_equiv (Subgroup.subgroupOfEquivOfLe hTbX).symm
    obtain ⟨k, hk⟩ := hTbp ⟨t, ht⟩
    apply hc k
    have : ψ ((⟨t, ht⟩ : ↥(Tb.subgroupOf X)) ^ 2 ^ k : ↥(Tb.subgroupOf X)) = c ^ 2 ^ k := by
      rw [← htc]; simp [map_pow]
    rw [← this, hk]; simp
  obtain ⟨haX, haψ⟩ := haψ
  obtain ⟨haX', hsa⟩ := hP A hAX hA a haA
  refine fun x hx => ?_
  obtain ⟨hxX, hsx⟩ := hP L hLX hL x hx
  obtain ⟨k, hk⟩ := perm3_alt_pow (ψ ⟨x, hxX⟩) (ψ ⟨a, haX⟩) hsx hsa haψ
  set y : G := (a ^ (k : ℕ))⁻¹ * x with hy
  have hakL : a ^ (k : ℕ) ∈ L := Subgroup.pow_mem _ (hAL haA) _
  have hakX : a ^ (k : ℕ) ∈ X := hLX hakL
  have hyL : y ∈ L := L.mul_mem (L.inv_mem hakL) hx
  have hyX : y ∈ X := hLX hyL
  have hψy : ψ ⟨y, hyX⟩ = 1 := by
    have h1 : (⟨y, hyX⟩ : ↥X) = (⟨a ^ (k : ℕ), hakX⟩ : ↥X)⁻¹ * ⟨x, hxX⟩ := rfl
    have h2 : ψ ⟨a ^ (k : ℕ), hakX⟩ = (ψ ⟨a, haX⟩) ^ (k : ℕ) := by
      have : (⟨a ^ (k : ℕ), hakX⟩ : ↥X) = (⟨a, haX⟩ : ↥X) ^ (k : ℕ) := rfl
      rw [this, map_pow]
    rw [h1, map_mul, map_inv, h2, hk, inv_mul_cancel]
  have hyQ : y ∈ pCoreOf 2 X := (hψker ⟨y, hyX⟩).mp hψy
  have hyLQ : y ∈ L ⊓ pCoreOf 2 X := ⟨hyL, hyQ⟩
  have hLQ : L ⊓ pCoreOf 2 X ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 X).to_le inf_le_right)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hgL := (Subgroup.mem_normalizer_iff.mp (hXL (hLX hg)) z)
    have hgQ := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X (hLX hg)) z)
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hgL.mp h1, hgQ.mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨hgL.mpr h1, hgQ.mpr h2⟩
  have hx_eq : x = a ^ (k : ℕ) * y := by rw [hy]; group
  rw [hx_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ haA _))
    (Subgroup.mem_sup_right (hLQ hyLQ))

omit [Finite G] in
theorem eq_sup_lI_sup {T M I₀ A B C : Subgroup G} (hA : oTwoUpper A = A)
    (hAL : A ≤ yOfL22 T M) (hI₀ : I₀ = (A ⊔ B) ⊔ (C ⊔ B)) (hB : T ⊓ I₀ = B) :
    I₀ = (lI T M I₀ ⊔ (T ⊓ I₀)) ⊔ (C ⊔ B) := by
  rw [hB]
  have hAI : A ≤ I₀ := by rw [hI₀]; exact le_sup_left.trans le_sup_left
  have hBI : B ≤ I₀ := by rw [hI₀]; exact le_sup_right.trans le_sup_left
  have hCI : C ⊔ B ≤ I₀ := by rw [hI₀]; exact le_sup_right
  have hlIle : lI T M I₀ ≤ I₀ := (oTwoUpper_le _).trans inf_le_right
  have hAlI : A ≤ lI T M I₀ := by
    calc A = oTwoUpper A := hA.symm
      _ ≤ oTwoUpper (yOfL22 T M ⊓ I₀) := oTwoUpper_mono (le_inf hAL hAI)
  apply le_antisymm
  · conv_lhs => rw [hI₀]
    refine sup_le (sup_le ?_ ?_) le_sup_right
    · exact hAlI.trans (le_sup_left.trans le_sup_left)
    · exact (le_sup_right : B ≤ lI T M I₀ ⊔ B).trans le_sup_left
  · exact sup_le (sup_le hlIle hBI) hCI

namespace Setting146

variable {T M : Subgroup G}

theorem T_le_normalizer_V (S : Setting146 G T M) : T ≤ Subgroup.normalizer (VZ T M : Set G) :=
  S.hyp.m_max.1.2.trans S.hyp1281.isTwoReducedIn.1.2.1

theorem oTwoUpper_le_centralizer (S : Setting146 G T M) {H H₂ : Subgroup G} (hH : IsHTM T M H)
    {u : G}
    (hH₂ : H₂ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u)) :
    oTwoUpper H₂ ≤ Subgroup.centralizer ({u} : Set G) := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxH₂, hxodd⟩ := hx
  obtain ⟨hxH, -, hxc⟩ := hH₂ hxH₂
  have hz : x * u * x⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := hxc u (Subgroup.mem_zpowers u)
  have h := commute_of_odd_orderOf S.card_Z (S.le_mcOf hH hxH) hz hxodd
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.mp hw]
  exact h.symm

end Setting146

theorem stepB (h9 : Stage1469) (h66 : Stage1466Six) (h661 : Stage1466One)
    (h105 : Stage14610Five) {T M : Subgroup G} (S : Setting146 G T M)
    (hD : FinalData146 T M) : False := by
  obtain ⟨H, u, H₂, hH, hu, hCu, h4, hm, hT0, hH₂C, hS3, hH₂M, hchief, hrk⟩ := hD
  obtain ⟨I, hI, hIc⟩ := exists_isIStar_choice hCu
  have hTH : T ≤ H := hH.1.1
  have hlIL : lI T M I ≤ yOfL22 T M := (oTwoUpper_le _).trans inf_le_left
  have hlII : lI T M I ≤ I := (oTwoUpper_le _).trans inf_le_right
  obtain ⟨h211, hLT⟩ := h9 G T M H u S hH hu I hI h4 hm
  have hL_eq : yOfL22 T M = lI T M I ⊔ pCoreOf 2 (yOfL22 T M) := by
    refine le_antisymm ?_ (sup_le hlIL (LieType.BorelTits.pCoreOf_le 2 _))
    refine le_sup_pCoreOf_of_S3 (X := yOfL22 T M ⊔ T) le_sup_left ?_ S.hyp1281.residual
      (oTwoUpper_oTwoUpper _) hlIL S.facts.sThree (S.hyp.sylow.1.to_le inf_le_left)
      (inf_le_left.trans le_sup_right) hLT
    exact sup_le Subgroup.le_normalizer (S.hyp.m_max.1.2.trans S.hyp1281.normal)
  have h29 : 2 ^ 9 < Nat.card T :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h211
  obtain ⟨hI₀, hGT⟩ := h66 G T M H u S hH hu I hI h29 hL_eq H₂ hT0 hH₂C hS3 hH₂M hchief
  have hTI_le : T ⊓ I ≤ (lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)) :=
    le_sup_right.trans le_sup_left
  obtain ⟨-, hTI₀⟩ := hI.of_le_inf hI₀.1 hTI_le
  have hTIH₂ : T ⊓ I ≤ H₂ := by
    refine le_trans ?_ hT0
    rcases h661 G T M H u S hH hu I hI with h | h
    · rw [h]; exact tU_le_tZero T u
    · exact h.le
  have hOc : oTwoUpper H₂ ≤ Subgroup.centralizer ({u} : Set G) :=
    S.oTwoUpper_le_centralizer hH hH₂C
  have hH₂H : H₂ ≤ H := hH₂C.trans (centralizerMod_le_left _ _ _)
  have hI₂H : oTwoUpper H₂ ⊔ (T ⊓ I) ≤ H :=
    sup_le ((oTwoUpper_le H₂).trans hH₂H) (inf_le_left.trans hTH)
  have hI₀eq := eq_sup_lI_sup (T := T) (M := M) (A := lI T M I) (B := T ⊓ I)
    (C := oTwoUpper H₂) (oTwoUpper_oTwoUpper _) hlIL rfl hTI₀
  have hcent : T ⊓ ((lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I))) = tU T u →
      (lI T M I ⊔ (T ⊓ I)) ⊔ (oTwoUpper H₂ ⊔ (T ⊓ I)) ≤ Subgroup.centralizer ({u} : Set G) := by
    intro h
    have hIT : T ⊓ I = tU T u := by rw [← hTI₀]; exact h
    have hIc' := hIc hIT
    exact sup_le (sup_le (hlII.trans hIc') (inf_le_right.trans hIc'))
      (sup_le hOc (inf_le_right.trans hIc'))
  have hrank := h105 G T M H u S hH hu _ hI₀ h4 hm (oTwoUpper H₂ ⊔ (T ⊓ I))
    (by rw [hTI₀]; exact le_sup_right) hI₂H hGT.2.2.1 hI₀eq hcent
  have hconj : conjClosure (VZ T M) (oTwoUpper H₂ ⊔ (T ⊓ I)) =
      conjClosure (VZ T M) (oTwoUpper H₂) :=
    conjClosure_sup_eq_of_normalizes (hTIH₂.trans (le_normalizer_oTwoUpper H₂))
      (inf_le_left.trans S.T_le_normalizer_V)
  rw [hconj, hrk] at hrank
  norm_num at hrank

@[expose] def Stage146BranchA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    (∃ H : Subgroup G, IsHTM T M H ∧ ¬ OddCoreModTwoTrivial H) → FinalData146 T M

@[expose] def Stage146BranchB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    (∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H) → FinalData146 T M

theorem stageSection146_of_parts (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hA : Stage146BranchA) (hB : Stage146BranchB) (h9 : Stage1469) (h66 : Stage1466Six)
    (h661 : Stage1466One) (h105 : Stage14610Five) : StageSection146 := by
  intro G _ _ T M hyp hnot hab
  have S : Setting146 G T M := ⟨hyp, hyp.facts1422 h11 h113, hnot, hab⟩
  by_cases h : ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H
  · exact stepB h9 h66 h661 h105 S (hB G T M S h)
  · push Not at h
    exact stepB h9 h66 h661 h105 S (hA G T M S h)

end CFSG.Quasithin
