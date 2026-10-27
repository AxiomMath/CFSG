module

public import CFSG.Quasithin.Background.FFC6L
public import CFSG.Quasithin.Background.B69Comp
public import CFSG.Quasithin.Background.FFC6F
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Equiv Equiv.Perm
open scoped commutatorElement

namespace B59

section Odd

variable {M : Type} [CommGroup M]

theorem exists_odd_of_perfect {X K Ab : Subgroup (MulAut M)} (hKX : K ≤ X) (hAX : Ab ≤ X)
    (hKperf : Group.IsPerfect ↥K) (hsup : X = K ⊔ Ab) {π : Perm (Fin 5) →* ↥X}
    (hinj : Function.Injective π) (hπs : Function.Surjective π) :
    ∃ σ : Perm (Fin 5), sign σ = -1 ∧ ((π σ : ↥X) : MulAut M) ∈ Ab := by
  by_contra hcon
  push Not at hcon
  let A5 : Subgroup ↥X := (alternatingGroup (Fin 5)).map π
  have hAb5 : Ab.subgroupOf X ≤ A5 := by
    intro x hx
    obtain ⟨σ, hσ⟩ := hπs x
    have hsg : sign σ = 1 := by
      rcases Int.units_eq_one_or (sign σ) with h | h
      · exact h
      · exact absurd (by rw [hσ]; exact hx) (hcon σ h)
    exact ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsg, hσ⟩
  let eπ : Perm (Fin 5) ≃* ↥X := MulEquiv.ofBijective π ⟨hinj, hπs⟩
  let ψ : ↥K →* ℤˣ := (Equiv.Perm.sign).comp (eπ.symm.toMonoidHom.comp (Subgroup.inclusion hKX))
  have hψ : ∀ k : ↥K, ψ k = 1 := by
    intro k
    have h1 : commutator ↥K ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
    have h2 : k ∈ commutator ↥K := by
      rw [hKperf.commutator_eq_top]
      trivial
    exact h1 h2
  have hK5 : K.subgroupOf X ≤ A5 := by
    intro x hx
    have h1 : sign (eπ.symm x) = 1 := hψ ⟨(x : MulAut M), hx⟩
    exact ⟨eπ.symm x, Equiv.Perm.mem_alternatingGroup.2 h1, eπ.apply_symm_apply x⟩
  have htop : (⊤ : Subgroup ↥X) ≤ A5 := by
    have h1 : (K ⊔ Ab).subgroupOf X = K.subgroupOf X ⊔ Ab.subgroupOf X :=
      Subgroup.subgroupOf_sup hKX hAX
    have h2 : (K ⊔ Ab).subgroupOf X = ⊤ := by
      rw [← hsup]
      exact Subgroup.subgroupOf_self X
    rw [← h2, h1]
    exact sup_le hK5 hAb5
  obtain ⟨σ', hσ'A, hσ'⟩ := htop (Subgroup.mem_top (π (Equiv.swap (0 : Fin 5) 1)))
  have h1 : σ' = Equiv.swap (0 : Fin 5) 1 := hinj hσ'
  have hs := Equiv.Perm.mem_alternatingGroup.1 hσ'A
  rw [h1, Equiv.Perm.sign_swap (by decide)] at hs
  exact absurd hs (by decide)

end Odd

section Main

variable {M : Type} [CommGroup M] [Finite M] {X : Subgroup (MulAut M)} {U : Subgroup M}
  {π : Perm (Fin 5) →* ↥X} {q : M →* G6.PermMod 5}

omit [Finite M] in
theorem card_M_eq (hqs : ∀ w, q w ∈ G6.coreMod 5) (hqr : ∀ m ∈ G6.coreMod 5, ∃ w, q w = m)
    (hqk : ∀ w, q w = 1 ↔ w ∈ fixV X) : Nat.card M = 16 * Nat.card ↥(fixV X) := by
  have hker : q.ker = fixV X := by
    ext w
    exact hqk w
  have hrange : q.range = G6.coreMod 5 := by
    ext m
    constructor
    · rintro ⟨w, rfl⟩
      exact hqs w
    · intro hm
      obtain ⟨w, hw⟩ := hqr m hm
      exact ⟨w, hw⟩
  have h1 := Subgroup.card_ker_mul_card_range q
  have h2 : Nat.card q.range = 16 :=
    (congrArg (fun S : Subgroup (G6.PermMod 5) => Nat.card S) hrange).trans card_coreMod_five
  rw [hker, h2] at h1
  rw [← h1]
  ring

omit [Finite M] in
theorem card_range_commMap_le {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) (h3 : sign σ = -1)
    (hUinv : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) (hα : U ⊔ fixV X = ⊤) (hUX : U ⊓ fixV X = ⊥)
    (hqs : ∀ w, q w ∈ G6.coreMod 5) (hqk : ∀ w, q w = 1 ↔ w ∈ fixV X)
    (hqe : ∀ (γ : Perm (Fin 5)) (w : M), q (((π γ : ↥X) : MulAut M) w) = G6.permAct 5 γ (q w)) :
    Nat.card (commMap ((π σ : ↥X) : MulAut M)).range ≤ 2 := by
  have haX : ((π σ : ↥X) : MulAut M) ∈ X := (π σ).2
  have hcU : ∀ w : M, commMap ((π σ : ↥X) : MulAut M) w ∈ U := by
    intro w
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 (hα ▸ Subgroup.mem_top w)
    have hca : ((π σ : ↥X) : MulAut M) c = c := hc _ haX
    rw [commMap_apply, map_mul, hca]
    have : ((π σ : ↥X) : MulAut M) u * c * (u * c)⁻¹ = ((π σ : ↥X) : MulAut M) u * u⁻¹ := by
      group
    rw [this]
    exact U.mul_mem (hUinv _ haX u hu) (U.inv_mem hu)
  refine (card_le_of_inj_maps_into q (commMap ((π σ : ↥X) : MulAut M)).range ?_ (commS σ) ?_).trans
    (card_commS_le h1 h2 h3)
  · rintro _ ⟨w, rfl⟩ hq1
    have hmem : commMap ((π σ : ↥X) : MulAut M) w ∈ U ⊓ fixV X := ⟨hcU w, (hqk _).1 hq1⟩
    rw [hUX, Subgroup.mem_bot] at hmem
    exact hmem
  · rintro _ ⟨w, rfl⟩
    rw [commMap_apply, map_mul, map_inv, hqe σ w]
    exact mem_commS (hqs w)

omit [Finite M] in
theorem card_le_two_mul_fixV_zpowers {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) (h3 : sign σ = -1)
    (hUinv : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) (hα : U ⊔ fixV X = ⊤) (hUX : U ⊓ fixV X = ⊥)
    (hqs : ∀ w, q w ∈ G6.coreMod 5) (hqk : ∀ w, q w = 1 ↔ w ∈ fixV X)
    (hqe : ∀ (γ : Perm (Fin 5)) (w : M), q (((π γ : ↥X) : MulAut M) w) = G6.permAct 5 γ (q w)) :
    Nat.card M ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers ((π σ : ↥X) : MulAut M))) := by
  have hr := card_range_commMap_le h1 h2 h3 hUinv hα hUX hqs hqk hqe
  have h := Subgroup.card_ker_mul_card_range (commMap ((π σ : ↥X) : MulAut M))
  rw [ker_commMap] at h
  calc Nat.card M = Nat.card ↥(fixV (Subgroup.zpowers ((π σ : ↥X) : MulAut M))) *
        Nat.card (commMap ((π σ : ↥X) : MulAut M)).range := h.symm
    _ ≤ Nat.card ↥(fixV (Subgroup.zpowers ((π σ : ↥X) : MulAut M))) * 2 := Nat.mul_le_mul_left _ hr
    _ = 2 * Nat.card ↥(fixV (Subgroup.zpowers ((π σ : ↥X) : MulAut M))) := mul_comm _ _

theorem isFFStarOffender_zpowers {a : MulAut M} (haX : a ∈ X) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hlow : Nat.card M ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers a))) :
    IsFFStarOffender X (Subgroup.zpowers a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  refine ⟨Subgroup.zpowers_le.2 haX, ?_, isElemAbelian2_zpowers ha2, fun B hB => ?_⟩
  · intro h
    apply ha1
    have : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · have hdvd : Nat.card ↥B ∣ 2 := hcard ▸ Subgroup.card_dvd_of_le hB
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · have : B = ⊥ := Subgroup.card_eq_one.1 h
      rw [this, B1.fixV_bot, Subgroup.card_bot, Subgroup.card_top, one_mul, hcard]
      exact hlow
    · have : B = Subgroup.zpowers a := Subgroup.eq_of_le_of_card_ge hB (by rw [h, hcard])
      rw [this]

omit [Finite M] in
theorem card_dvd_twelve {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) (h3 : sign σ = -1)
    {Ab : Subgroup (MulAut M)} (hAbX : Ab ≤ X) (hel : IsElemAbelian2 Ab)
    (hπinj : Function.Injective π) (hπs : Function.Surjective π)
    (haAb : ((π σ : ↥X) : MulAut M) ∈ Ab) : Nat.card Ab ∣ 12 := by
  let ι : Perm (Fin 5) →* MulAut M := X.subtype.comp π
  have hι : Function.Injective ι := X.subtype_injective.comp hπinj
  set P : Subgroup (Perm (Fin 5)) := Ab.comap ι with hP
  have hPcard : Nat.card P = Nat.card Ab := by
    have hle : Ab ≤ ι.range := by
      intro x hx
      obtain ⟨τ, hτ⟩ := hπs ⟨x, hAbX hx⟩
      exact ⟨τ, congrArg Subtype.val hτ⟩
    have h5 : P.map ι = Ab := by
      rw [hP, Subgroup.map_comap_eq, inf_eq_right.2 hle]
    calc Nat.card P = Nat.card (P.map ι) := (Subgroup.card_map_of_injective hι).symm
      _ = Nat.card Ab := by rw [h5]
  have hPle : P ≤ Subgroup.centralizer ({σ} : Set (Perm (Fin 5))) := by
    intro τ hτ
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    rw [map_mul, map_mul]
    exact hel.1 _ hτ _ haAb
  have := Subgroup.card_dvd_of_le hPle
  rw [card_centralizer_odd h1 h2 h3, hPcard] at this
  exact this


theorem caseB_M {K Ab : Subgroup (MulAut M)} (hKX : K ≤ X) (hKperf : Group.IsPerfect ↥K)
    (hsup : X = K ⊔ Ab) (hmin : IsFFStarMin X Ab) (hα : commV K ⊔ fixV X = ⊤)
    (hfc : fixV K ⊓ commV K = ⊥) (hS : SymmetricNatural X (commV K) (fixV K ⊓ commV K) 5) :
    Nat.card Ab = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ⟩ : ∃ π : Perm (Fin 5) →* ↥X,
      (FFModel.symDn 5).RealizesVia X (commV K) ⊥ π := by
    obtain ⟨π, hπ⟩ := hS
    rw [hfc] at hπ
    exact ⟨π, hπ⟩
  have hinj : Function.Injective π := injective_of_faithful_sec (symDn_faithful (by norm_num)) hπ
  have hπs : Function.Surjective π := hπ.1
  have hUinv : ∀ g ∈ X, ∀ u ∈ commV K, g u ∈ commV K := fun g hg u hu => hπ.2.2.2.1 ⟨g, hg⟩ u hu
  have hUX : commV K ⊓ fixV X = ⊥ := by
    have : commV K ⊓ fixV X ≤ fixV K ⊓ commV K := fun x hx => ⟨B1.fixV_le_fixV hKX hx.2, hx.1⟩
    exact le_bot_iff.1 (le_of_le_of_eq this hfc)
  obtain ⟨q, hqs, hqr, hqk, hqe⟩ : ∃ q : M →* G6.PermMod 5, (∀ w, q w ∈ G6.coreMod 5) ∧
      (∀ m ∈ G6.coreMod 5, ∃ w, q w = m) ∧ (∀ w, q w = 1 ↔ w ∈ fixV X) ∧
      ∀ (γ : Perm (Fin 5)) (w : M), q (((π γ : ↥X) : MulAut M) w) = G6.permAct 5 γ (q w) :=
    exists_modelHom symDn_ker_five hπ hα hUX
  have hMc := card_M_eq hqs hqr hqk
  obtain ⟨σ, hσs, haAb⟩ := exists_odd_of_perfect hKX hmin.1.1 hKperf hsup hinj hπs
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact absurd hσs (by simp)
  have ha2 : ((π σ : ↥X) : MulAut M) ^ 2 = 1 := hmin.1.2.2.1.2 _ haAb
  have hσ2 : σ * σ = 1 := by
    apply hinj
    apply Subtype.ext
    rw [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact ha2
  have ha1 : ((π σ : ↥X) : MulAut M) ≠ 1 := by
    intro h
    apply hσ1
    apply hinj
    apply Subtype.ext
    rw [map_one, Subgroup.coe_one]
    exact h
  have haX : ((π σ : ↥X) : MulAut M) ∈ X := (π σ).2
  have hlow := card_le_two_mul_fixV_zpowers hσ1 hσ2 hσs hUinv hα hUX hqs hqk hqe
  have hB : IsFFStarOffender X (Subgroup.zpowers ((π σ : ↥X) : MulAut M)) :=
    isFFStarOffender_zpowers haX ha1 ha2 hlow
  have hBAb : Subgroup.zpowers ((π σ : ↥X) : MulAut M) ≤ Ab := Subgroup.zpowers_le.2 haAb
  have hordB : Nat.card ↥(Subgroup.zpowers ((π σ : ↥X) : MulAut M)) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  have hdvd : Nat.card Ab ∣ 12 :=
    card_dvd_twelve hσ1 hσ2 hσs hmin.1.1 hmin.1.2.2.1 hinj hπs haAb
  obtain ⟨m, hm⟩ := hmin.1.2.2.1.isPGroup.exists_card_eq
  have hAb2 : 2 ≤ Nat.card Ab := hordB ▸ Subgroup.card_le_of_le hBAb
  by_contra hne
  have hAb4 : Nat.card Ab = 4 := by
    have hm2 : m ≤ 2 := by
      by_contra hm3
      have h8 : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega)).trans (hm ▸ hdvd)
      norm_num at h8
    interval_cases m <;> simp_all
  have hnle : ¬ Ab ≤ Subgroup.zpowers ((π σ : ↥X) : MulAut M) := by
    intro h
    have := Subgroup.card_le_of_le h
    omega
  obtain ⟨b, hbA, hb⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  have hab : ((π σ : ↥X) : MulAut M) ≠ b := fun h => hb (h ▸ Subgroup.mem_zpowers _)
  obtain ⟨τ, hτ⟩ := hπs ⟨b, hmin.1.1 hbA⟩
  have hτe : ((π τ : ↥X) : MulAut M) = b := congrArg Subtype.val hτ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact hb1 (by rw [← hτe, map_one, Subgroup.coe_one])
  have hτ2 : τ * τ = 1 := by
    apply hinj
    apply Subtype.ext
    rw [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, hτe, ← pow_two]
    exact hmin.1.2.2.1.2 b hbA
  have hστ : σ ≠ τ := by
    rintro rfl
    exact hab hτe
  have hcomm : σ * τ = τ * σ := by
    apply hinj
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hτe]
    exact hmin.1.2.2.1.1 _ haAb b hbA
  have hS2 : ∀ k ∈ fixV Ab, q k ∈ fixS₂ σ τ := by
    intro k hk
    have hak : ((π σ : ↥X) : MulAut M) k = k := hk _ haAb
    have hbk : ((π τ : ↥X) : MulAut M) k = k := by
      rw [hτe]
      exact hk b hbA
    refine mem_fixS₂ (hqs k) ?_ ?_
    · have h1 := hqe σ k
      rw [hak] at h1
      exact h1.symm
    · have h1 := hqe τ k
      rw [hbk] at h1
      exact h1.symm
  have hfix : Nat.card ↥(fixV Ab) ≤ Nat.card ↥(fixV X) * 4 := by
    have h1 := card_le_of_maps_into q (fixV Ab) (fixS₂ σ τ) hS2
    have hker : q.ker = fixV X := by
      ext w
      exact hqk w
    rw [hker] at h1
    exact h1.trans (Nat.mul_le_mul_left _ (card_fixS₂_le_four hσ1 hτ1 hστ hσ2 hτ2 hcomm hσs))
  have hoffAb := hmin.1.2.2.2 _ hBAb
  have hup : Nat.card Ab * Nat.card ↥(fixV Ab) ≤ Nat.card M := by
    calc Nat.card Ab * Nat.card ↥(fixV Ab) ≤ 4 * (Nat.card ↥(fixV X) * 4) :=
          Nat.mul_le_mul (le_of_eq hAb4) hfix
      _ = Nat.card M := by rw [hMc]; ring
  have heq : Nat.card ↥(Subgroup.zpowers ((π σ : ↥X) : MulAut M)) *
      Nat.card ↥(fixV (Subgroup.zpowers ((π σ : ↥X) : MulAut M))) =
        Nat.card Ab * Nat.card ↥(fixV Ab) := by
    refine le_antisymm hoffAb ?_
    calc Nat.card Ab * Nat.card ↥(fixV Ab) ≤ Nat.card M := hup
      _ ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers ((π σ : ↥X) : MulAut M))) := hlow
      _ = _ := by rw [hordB]
  have hFFLe : FFLe X (Subgroup.zpowers ((π σ : ↥X) : MulAut M)) Ab :=
    ⟨hB.isA2, hmin.1.isA2, hBAb, heq⟩
  have hEq := hmin.2 _ hB hFFLe
  rw [← hEq, hordB] at hAb4
  omega

end Main

section CaseB

variable {V : Type} [CommGroup V] [Finite V]

theorem caseB (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥)
    (hmin : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G) (hLA : ⁅L, A⁆ = L)
    (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) (hXK : Xr L A ≠ Kr L A)
    (hα : commV (Kr L A) ⊔ fixV (Xr L A) = ⊤) (hfc : fixV (Kr L A) ⊓ commV (Kr L A) = ⊥)
    (hS : SymmetricNatural (Xr L A) (commV (Kr L A)) (fixV (Kr L A) ⊓ commV (Kr L A)) 5) :
    B59Case2 A L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hL hmin.1 hLA
  have hAG : A ≤ G := hmin.1.1
  have hLU : L ≤ stabSub (W0 L A) := le_sup_left.trans hst
  have hAU : A ≤ stabSub (W0 L A) := le_sup_right.trans hst
  have hfaithL := faithL hV hO2 hL hmin hLA
  obtain ⟨-, -, hLbq, hLbH, -, -, hoff, -, hsup⟩ := red_aut hV hL hmin.1 hLA
  have hmin' : IsFFStarMin (Xr L A) (Ar L A) := red_min hV hL hmin hLA
  have hVM : ∀ v : ↥(W0 L A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  have hKperf : Group.IsPerfect ↥(Kr L A) := ⟨hLbq.1⟩
  have hcard : Nat.card ↥(Ar L A) = 2 := caseB_M hLbH hKperf hsup hmin' hα hfc hS
  have hr : (1 : ℚ) ≤ rAV (Ar L A) :=
    not_lt.1 (CFSG.Quasithin.B69.not_rAV_lt_one_of_card_two hVM hmin'.1.isA2 hcard)
  obtain ⟨hsupV, hfA⟩ := lift_q hV hL hmin hLA hr
  have hMU : commV (Kr L A) ⊔ fixV (Ar L A) = ⊤ :=
    top_le_iff.1 (hα ▸ sup_le_sup_left (B1.fixV_le_fixV hoff.1) _)
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl => hn a (hAG ha) l hl
  obtain ⟨hVU, hcommV, -, -⟩ := lift_V hLU hAU hAn hLA hsupV hMU
  have hfA' : ∀ g ∈ A, (∀ v ∈ W0 L A, g v = v) → g = 1 := fun g hg hgW => by
    have : g ∈ A ⊓ centSub (W0 L A) := ⟨hg, hgW⟩
    rw [hfA, Subgroup.mem_bot] at this
    exact this
  have hcardA : Nat.card ↥A = 2 := (card_autSub_eq hAU hfA').symm.trans hcard
  have hAK : ¬ Ar L A ≤ Kr L A := fun h => hXK (by rw [hsup]; exact sup_eq_left.2 h)
  have hĀK : Ar L A ⊓ Kr L A = ⊥ := by
    have hdvd : Nat.card ↥(Ar L A ⊓ Kr L A) ∣ 2 := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact Subgroup.card_eq_one.1 h
    · exfalso
      apply hAK
      have : Ar L A ⊓ Kr L A = Ar L A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
      exact inf_eq_left.1 this
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hfLA : ∀ g ∈ L ⊔ A, (∀ v ∈ W0 L A, g v = v) → g = 1 := by
    intro g hg hgW
    obtain ⟨l, hl, a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hg
    have hlK : resHom (W0 L A) ⟨l, hLU hl⟩ ∈ Kr L A := mem_autSub.2 ⟨⟨l, hLU hl⟩, hl, rfl⟩
    have haA : resHom (W0 L A) ⟨a, hAU ha⟩ ∈ Ar L A := mem_autSub.2 ⟨⟨a, hAU ha⟩, ha, rfl⟩
    have hprod : resHom (W0 L A) ⟨l, hLU hl⟩ * resHom (W0 L A) ⟨a, hAU ha⟩ = 1 := by
      ext w
      exact hgW w w.2
    have hā : resHom (W0 L A) ⟨a, hAU ha⟩ ∈ Kr L A := by
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact (Kr L A).inv_mem hlK
    have h0 : resHom (W0 L A) ⟨a, hAU ha⟩ ∈ Ar L A ⊓ Kr L A := ⟨haA, hā⟩
    rw [hĀK, Subgroup.mem_bot] at h0
    have ha1 : a = 1 := hfA' a ha fun v hv => by
      exact congrArg (fun φ : MulAut ↥(W0 L A) => ((φ ⟨v, hv⟩ : ↥(W0 L A)) : V)) h0
    subst ha1
    have hl1 : l = 1 := hfaithL l hl fun v hv => by simpa using hgW v hv
    subst hl1
    simp
  have e : ↥(L ⊔ A) ≃* ↥(Xr L A) := resEquiv hst hfLA
  obtain ⟨π, hπ⟩ := hS
  have hinj : Function.Injective π := injective_of_faithful_sec (symDn_faithful (by norm_num)) hπ
  have hπs : Function.Surjective π := hπ.1
  have eπ : Perm (Fin 5) ≃* ↥(Xr L A) := MulEquiv.ofBijective π ⟨hinj, hπs⟩
  refine ⟨⟨e.trans eπ.symm⟩, hcardA, ?_, ?_⟩
  · have hreal := realizes_map hst hfLA (D := FFModel.symDn 5) ⟨π, hπ⟩
    rw [hfc, Subgroup.map_bot, map_commV_aut hLU, ← hcommV] at hreal
    exact hreal
  · rw [hcommV]
    exact hVU

end CaseB

end B59

end FFC

end CFSG.Quasithin
