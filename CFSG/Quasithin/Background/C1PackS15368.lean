module

public import CFSG.Quasithin.EmptyFaithful.T1531In68b
public import CFSG.Quasithin.Background.C1PackS15367
public import CFSG.Quasithin.Background.C1PackSL2
public import CFSG.Quasithin.EmptyFaithful.T1531Close2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace C1Pack153

section TwoThree

variable {G : Type} [Group G] [Finite G]

@[expose] def TwoThree (K : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p = 2 ∨ p = 3

omit [Finite G] in
theorem TwoThree.mono {K K' : Subgroup G} (h : K ≤ K') (hK' : TwoThree K') : TwoThree K :=
  fun p hp hd => hK' p hp (hd.trans (Subgroup.card_dvd_of_le h))

theorem twoThree_of_isPGroup {K : Subgroup G} (hK : IsPGroup 2 K) : TwoThree K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro p hp hd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hK
  rw [hn] at hd
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

omit [Finite G] in
theorem TwoThree.sup {A B : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hA : TwoThree A)
    (hB : TwoThree B) : TwoThree (A ⊔ B) := by
  intro p hp hd
  have h := S143.card_sup_mul_card_inf_of_le_normalizer hBA
  have hd' : p ∣ Nat.card A * Nat.card B := by
    rw [← h]
    exact hd.mul_right _
  exact (hp.dvd_mul.mp hd').elim (hA p hp) (hB p hp)

omit [Finite G] in
theorem TwoThree.conj {A : Subgroup G} (hA : TwoThree A) (g : G) : TwoThree (conjSubgroup A g) := by
  intro p hp hd
  rw [E3.card_conjSubgroup] at hd
  exact hA p hp hd

theorem twoThree_of_relIndex {K : Subgroup G} {n : ℕ} (hn : n = 3 ∨ n = 9)
    (hr : (pCoreOf 2 K).relIndex K = n) : TwoThree K := by
  have h2 : TwoThree (pCoreOf 2 K) := twoThree_of_isPGroup (pCoreOf_isPGroup 2 K)
  intro p hp hd
  have h := Subgroup.relIndex_mul_card (pCoreOf 2 K) K
  rw [inf_eq_left.mpr (pCoreOf_le 2 K), hr] at h
  rw [← h] at hd
  rcases hp.dvd_mul.mp hd with h1 | h1
  · rcases hn with rfl | rfl
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h1)
    · have : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by norm_num at h1 ⊢; exact h1)
      exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this)
  · exact h2 p hp h1

theorem isPGroup_two_of_factor {X C N : Subgroup G} (hCX : C ≤ X) (hNX : N ≤ X)
    (hCn : X ≤ Subgroup.normalizer (C : Set G))
    (hfac : ∀ x ∈ X, ∃ n ∈ N, ∃ c ∈ C, x = n * c)
    (hC : TwoThree C) (hN : TwoThree N) (h3 : ¬ 3 ∣ Nat.card X) : IsPGroup 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (C.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hCn
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf X)
  have hCsub : Nat.card ↥(C.subgroupOf X) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
  let φ : ↥N →* ↥X ⧸ C.subgroupOf X :=
    (QuotientGroup.mk' (C.subgroupOf X)).comp (Subgroup.inclusion hNX)
  have hφ : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨n, hn, c, hc, hxnc⟩ := hfac x x.2
      refine ⟨⟨n, hn⟩, ?_⟩
      have hxe : x = ⟨n, hNX hn⟩ * ⟨c, hCX hc⟩ := Subtype.ext hxnc
      show QuotientGroup.mk (⟨n, hNX hn⟩ : ↥X) = QuotientGroup.mk x
      rw [hxe, QuotientGroup.mk_mul]
      have h1 : (QuotientGroup.mk (⟨c, hCX hc⟩ : ↥X) : ↥X ⧸ C.subgroupOf X) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hc
      rw [h1, mul_one]
  have hdvd : Nat.card (↥X ⧸ C.subgroupOf X) ∣ Nat.card N := Subgroup.card_dvd_of_surjective hφ
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card X → p = 2 := by
    intro p hp hpd
    have hpd' := hpd
    rw [hcard, hCsub] at hpd'
    have h23 : p = 2 ∨ p = 3 := by
      rcases hp.dvd_mul.mp hpd' with h1 | h1
      · exact hN p hp (h1.trans hdvd)
      · exact hC p hp h1
    rcases h23 with h | h
    · exact h
    · exact absurd (h ▸ hpd) h3
  have hne : Nat.card X ≠ 0 := Nat.card_pos.ne'
  exact IsPGroup.of_card
    (Nat.eq_prime_pow_of_unique_prime_dvd hne fun {p} hp hpd => hprime p hp hpd)

end TwoThree

section Abstract

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_sup' {A K L : Subgroup G} (hK : A ≤ Subgroup.normalizer (K : Set G))
    (hL : A ≤ Subgroup.normalizer (L : Set G)) :
    A ≤ Subgroup.normalizer ((K ⊔ L : Subgroup G) : Set G) := by
  have hmap : ∀ g ∈ A, ∀ N : Subgroup G, g ∈ Subgroup.normalizer (N : Set G) →
      N.map (MulAut.conj g).toMonoidHom = N := by
    intro g hg N hgN
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by simp [mul_assoc]⟩
      have hg' : g⁻¹ ∈ Subgroup.normalizer (N : Set G) := (Subgroup.normalizer (N : Set G)).inv_mem hgN
      have := (Subgroup.mem_normalizer_iff.mp hg' y).mp hy
      simpa using this
  have key : ∀ g ∈ A, ∀ x ∈ K ⊔ L, g * x * g⁻¹ ∈ K ⊔ L := by
    intro g hg x hx
    have hx' : (MulAut.conj g) x ∈ (K ⊔ L).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [Subgroup.map_sup, hmap g hg K (hK hg), hmap g hg L (hL hg)] at hx'
    simpa using hx'
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have h0 := key g⁻¹ (A.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h0

theorem isSylowTwoOf_of_sup_normal {X P Q₀ T₀ : Subgroup G} (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hT₀X : T₀ ≤ X) (hT₀2 : IsPGroup 2 T₀) (hTP : T₀ ⊔ P = X) (hQT : Q₀ ≤ T₀) (hQP : Q₀ ≤ P)
    (hQsyl : IsSylowTwoOf Q₀ P) : IsSylowTwoOf T₀ X := by
  refine ⟨hT₀X, hT₀2, ?_⟩
  have hT₀N : T₀ ≤ Subgroup.normalizer (P : Set G) := hT₀X.trans hXP
  have hprod := S143.card_sup_mul_card_inf_of_le_normalizer hT₀N
  rw [sup_comm, hTP] at hprod
  have h1 := Subgroup.relIndex_mul_card T₀ X
  rw [inf_eq_left.mpr hT₀X] at h1
  have h2 := Subgroup.relIndex_mul_card Q₀ P
  rw [inf_eq_left.mpr hQP] at h2
  have hQPT : Q₀ ≤ P ⊓ T₀ := le_inf hQP hQT
  have h3 := Subgroup.relIndex_mul_card Q₀ (P ⊓ T₀)
  rw [inf_eq_left.mpr hQPT] at h3
  have hT0 : 0 < Nat.card T₀ := Nat.card_pos
  have hQ0 : 0 < Nat.card Q₀ := Nat.card_pos
  have habc : T₀.relIndex X * Q₀.relIndex (P ⊓ T₀) = Q₀.relIndex P := by
    have e : (T₀.relIndex X * Q₀.relIndex (P ⊓ T₀)) * (Nat.card T₀ * Nat.card Q₀) =
        Q₀.relIndex P * (Nat.card T₀ * Nat.card Q₀) := by
      calc (T₀.relIndex X * Q₀.relIndex (P ⊓ T₀)) * (Nat.card T₀ * Nat.card Q₀)
          = (T₀.relIndex X * Nat.card T₀) * (Q₀.relIndex (P ⊓ T₀) * Nat.card Q₀) := by ring
        _ = Nat.card X * Nat.card ↥(P ⊓ T₀) := by rw [h1, h3]
        _ = Nat.card P * Nat.card T₀ := hprod
        _ = (Q₀.relIndex P * Nat.card Q₀) * Nat.card T₀ := by rw [h2]
        _ = Q₀.relIndex P * (Nat.card T₀ * Nat.card Q₀) := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hT0 hQ0) e
  intro hd
  apply hQsyl.2.2
  have : (Q₀.subgroupOf P).index = Q₀.relIndex P := rfl
  rw [this, ← habc]
  exact hd.mul_right _

theorem isPGroup_two_of_thompson_factor
    {D TE P Q₀ Yf F Z V : Subgroup G}
    (hPD : P ≤ D) (hDP : D ≤ Subgroup.normalizer (P : Set G)) (hP3 : ¬ 3 ∣ Nat.card P)
    (hPs : Group.IsSolvable ↥P)
    (hQP : Q₀ ≤ P) (hQsyl : IsSylowTwoOf Q₀ P) (hDQ : D ≤ Subgroup.normalizer (Q₀ : Set G))
    (hQ2 : IsPGroup 2 Q₀)
    (hTED : TE ≤ D) (hTE2 : IsPGroup 2 TE) (hQTE : Q₀ ≤ TE)
    (hVQ : V ≤ Q₀) (hCV : IsPGroup 2 (Subgroup.centralizer (V : Set G)))
    (hYD : Yf ≤ D) (hYJ : Yf ≤ Subgroup.normalizer (thompsonJ TE : Set G))
    (hZQ : Z ≤ Q₀) (hZc : ∀ z ∈ Z, ∀ t ∈ TE, z * t = t * z) (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hF : ∀ f ∈ F, f ≠ 1 → ∃ y ∈ Yf, ∃ z ∈ Z, f = y * z * y⁻¹)
    (hCF : TwoThree (Subgroup.centralizer (F : Set G)))
    (hNJ : TwoThree (Subgroup.normalizer (thompsonJ TE : Set G))) : IsPGroup 2 P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J : Subgroup G := thompsonJ TE with hJdef
  have hJTE : J ≤ TE := thompsonJ_le_self TE
  have hJD : J ≤ D := hJTE.trans hTED
  have hJP : J ≤ Subgroup.normalizer (P : Set G) := hJD.trans hDP
  set X : Subgroup G := J ⊔ P with hXdef
  have hXD : X ≤ D := sup_le hJD hPD
  have hXP : X ≤ Subgroup.normalizer (P : Set G) := sup_le hJP Subgroup.le_normalizer
  have hPX : P ≤ X := le_sup_right
  have hJX : J ≤ X := le_sup_left
  have hXQ : X ≤ Subgroup.normalizer (Q₀ : Set G) := hXD.trans hDQ
  have hQX : Q₀ ≤ X := hQP.trans hPX
  have hJ2 : IsPGroup 2 J := hTE2.to_le hJTE
  have hX3 : ¬ 3 ∣ Nat.card X := by
    have h := S143.card_sup_mul_card_inf_of_le_normalizer hJP
    rw [sup_comm] at h
    intro hd
    have h' : 3 ∣ Nat.card P * Nat.card J := by
      rw [← h]
      exact hd.mul_right _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h' with h1 | h1
    · exact hP3 h1
    · obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hJ2
      rw [hn] at h1
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
      omega
  set T₀ : Subgroup G := TE ⊓ X with hT₀def
  have hT₀X : T₀ ≤ X := inf_le_right
  have hT₀TE : T₀ ≤ TE := inf_le_left
  have hJT₀ : J ≤ T₀ := le_inf hJTE hJX
  have hT₀2 : IsPGroup 2 T₀ := hTE2.to_le hT₀TE
  have hQT₀ : Q₀ ≤ T₀ := le_inf hQTE hQX
  have hTP : T₀ ⊔ P = X :=
    le_antisymm (sup_le hT₀X hPX) (sup_le (hJT₀.trans le_sup_left) le_sup_right |>.trans' le_rfl)
  have hT₀syl : IsSylowTwoOf T₀ X := isSylowTwoOf_of_sup_normal hXP hT₀X hT₀2 hTP hQT₀ hQP hQsyl
  have hJT₀eq : thompsonJ T₀ = J := (thompsonJ_eq_of_le hJT₀ hT₀TE).symm
  have hQpX : Q₀ ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hQX hXQ hQ2
  have hXchar : CharTwo X := by
    have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X
    have hXC : X ≤ Subgroup.normalizer
        (Subgroup.centralizer (pCoreOf 2 X : Set G) : Set G) := B2F.le_normalizer_centralizer hXN
    have hXK : X ≤ Subgroup.normalizer
        ((X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) : Subgroup G) : Set G) :=
      B2F.le_normalizer_inf Subgroup.le_normalizer hXC
    have hK2 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G)) :=
      hCV.to_le (inf_le_right.trans (Subgroup.centralizer_le (hVQ.trans hQpX)))
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hXK hK2
  have hXsolv : Group.IsSolvable ↥X := by
    have hnorm : (P.subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPX).mpr hXP
    have hNs : Group.IsSolvable ↥(P.subgroupOf X) :=
      Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hPX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPX).injective
    have : Group.IsNilpotent ↥J := hJ2.isNilpotent
    have hJs : Group.IsSolvable ↥J := inferInstance
    let φ : ↥J →* ↥X ⧸ P.subgroupOf X :=
      (QuotientGroup.mk' (P.subgroupOf X)).comp (Subgroup.inclusion hJX)
    have hφ : Function.Surjective φ := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        have hmul := Subgroup.coe_mul_of_right_le_normalizer_left P J hJP
        have hx : (x : G) ∈ P ⊔ J := by rw [sup_comm]; exact x.2
        have hx' : (x : G) ∈ (P : Set G) * (J : Set G) := by rw [← hmul]; exact hx
        obtain ⟨p, hp, j, hj, hpj⟩ := Set.mem_mul.mp hx'
        refine ⟨⟨j, hj⟩, ?_⟩
        have hxe : x = ⟨p, hPX hp⟩ * ⟨j, hJX hj⟩ := Subtype.ext hpj.symm
        show QuotientGroup.mk (⟨j, hJX hj⟩ : ↥X) = QuotientGroup.mk x
        rw [hxe, QuotientGroup.mk_mul]
        have h1 : (QuotientGroup.mk (⟨p, hPX hp⟩ : ↥X) : ↥X ⧸ P.subgroupOf X) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hp
        rw [h1, one_mul]
    have hquot : Group.IsSolvable (↥X ⧸ P.subgroupOf X) := Group.isSolvable_of_surjective hφ
    exact Group.isSolvable_of_ker_le_range (P.subgroupOf X).subtype
      (QuotientGroup.mk' (P.subgroupOf X)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  obtain ⟨hU, -, hcase, -⟩ := B2_16 (V := conjClosure (quasithinOmegaOneCenter T₀) X) hXsolv hXchar
    hT₀syl rfl
  set V₀ : Subgroup G := conjClosure (quasithinOmegaOneCenter T₀) X with hV₀def
  have hXV₀ : X ≤ Subgroup.normalizer (V₀ : Set G) := le_normalizer_conjClosure _ X
  have hJ₀ : thompsonJ T₀ ≤ Subgroup.centralizer (V₀ : Set G) := by
    rcases hcase with ⟨hJ, -⟩ | ⟨hJ, hI⟩
    · exact hJ
    · exfalso
      obtain ⟨I, hsyl, hdec, -, -, hnat, -⟩ := hI
      have hJN : thompsonJ T₀ ≤ Subgroup.normalizer (V₀ : Set G) :=
        (thompsonJ_le_self T₀).trans (hT₀X.trans hXV₀)
      have hne : autI hU (thompsonJ T₀) ≠ ⊥ := (autI_eq_bot_iff hU hJN).not.2 hJ
      have hne2 : autI hU (thompsonJ X) ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hsyl.1))
      have hIne : I.Nonempty := by
        by_contra hI0
        rw [Finset.not_nonempty_iff_eq_empty] at hI0
        apply hne2
        rw [hdec, hI0]
        simp
      obtain ⟨L, hL⟩ := hIne
      have hLle : L ≤ autI hU (thompsonJ X) := by
        rw [hdec]
        exact le_iSup₂ (f := fun (L' : Subgroup (MulAut (IntMod V₀ hU))) (_ : L' ∈ I) => L') L hL
      have hLcard : Nat.card L = 6 := by
        obtain ⟨e, -⟩ := hnat L hL
        rw [Nat.card_congr e.toEquiv]
        exact C1Pack.card_sl2F2
      have hdvd1 : Nat.card L ∣ Nat.card (autI hU X) :=
        Subgroup.card_dvd_of_le (hLle.trans (autI_mono hU (thompsonJ_le_self X)))
      have hdvd2 : Nat.card (autI hU X) ∣ Nat.card X :=
        Dvd.intro _ (card_autI_mul_card_inf hU hXV₀)
      apply hX3
      rw [hLcard] at hdvd1
      exact (show 3 ∣ 6 by norm_num).trans (hdvd1.trans hdvd2)
  obtain ⟨-, hfac⟩ := B2_7_of_le_factor hXV₀ hT₀syl hJ₀
  have hFV₀ : F ≤ V₀ := by
    intro f hf
    by_cases hf1 : f = 1
    · rw [hf1]
      exact V₀.one_mem
    obtain ⟨y, hy, z, hz, rfl⟩ := hF f hf hf1
    have hyN : y ∈ Subgroup.normalizer (X : Set G) :=
      le_normalizer_sup' hYJ (hYD.trans hDP) hy
    have hzTE : z ∈ TE := hQTE (hZQ hz)
    have hzT₀ : z ∈ T₀ := ⟨hzTE, hQX (hZQ hz)⟩
    have hzc : ∀ u ∈ T₀, z * u = u * z := fun u hu => hZc z hz u hu.1
    have hconjX : B6.conjSub y X = X := by
      ext x
      rw [B6.mem_conjSub]
      have := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hyN) x
      simpa using this.symm
    have hconjT : IsSylowTwoOf (B6.conjSub y T₀) X := by
      have := B6.isSylowTwoOf_conjSub hT₀syl y
      rwa [hconjX] at this
    obtain ⟨g, hgX, hg⟩ := B6.isSylowTwoOf_exists_conj hT₀syl hconjT
    have hyz : y * z * y⁻¹ ∈ B6.conjSub y T₀ := by
      rw [B6.mem_conjSub]
      simpa [mul_assoc] using hzT₀
    rw [hg] at hyz
    have hw : g⁻¹ * (y * z * y⁻¹) * g ∈ T₀ := B6.mem_conjSub.mp hyz
    have hwc : ∀ u ∈ T₀, (g⁻¹ * (y * z * y⁻¹) * g) * u = u * (g⁻¹ * (y * z * y⁻¹) * g) := by
      intro u hu
      have hu' : g * u * g⁻¹ ∈ B6.conjSub g T₀ := by
        rw [B6.mem_conjSub]
        simpa [mul_assoc] using hu
      rw [← hg] at hu'
      have hu'' : y⁻¹ * (g * u * g⁻¹) * y ∈ T₀ := B6.mem_conjSub.mp hu'
      have hc := hzc _ hu''
      calc (g⁻¹ * (y * z * y⁻¹) * g) * u
          = g⁻¹ * (y * (z * (y⁻¹ * (g * u * g⁻¹) * y)) * y⁻¹) * g := by group
        _ = g⁻¹ * (y * ((y⁻¹ * (g * u * g⁻¹) * y) * z) * y⁻¹) * g := by rw [hc]
        _ = u * (g⁻¹ * (y * z * y⁻¹) * g) := by group
    have hw2 : (g⁻¹ * (y * z * y⁻¹) * g) ^ 2 = 1 := by
      calc (g⁻¹ * (y * z * y⁻¹) * g) ^ 2 = g⁻¹ * y * (z * z) * y⁻¹ * g := by rw [pow_two]; group
        _ = 1 := by rw [hZ2 z hz]; group
    have hwΩ : g⁻¹ * (y * z * y⁻¹) * g ∈ quasithinOmegaOneCenter T₀ :=
      Subgroup.subset_closure ⟨⟨hw, Subgroup.mem_centralizer_iff.mpr fun u hu => (hwc u hu).symm⟩, hw2⟩
    have := mem_conjClosure hgX hwΩ
    simpa [mul_assoc] using this
  have hCsub : (X ⊓ Subgroup.centralizer (V₀ : Set G)) ≤ Subgroup.centralizer (F : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hFV₀)
  have hC : TwoThree (X ⊓ Subgroup.centralizer (V₀ : Set G)) := hCF.mono hCsub
  have hN : TwoThree (X ⊓ Subgroup.normalizer (thompsonJ T₀ : Set G)) := by
    rw [hJT₀eq]
    exact hNJ.mono inf_le_right
  have hXn : X ≤ Subgroup.normalizer
      ((X ⊓ Subgroup.centralizer (V₀ : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hXV₀)
  have hX2 : IsPGroup 2 X := isPGroup_two_of_factor inf_le_left inf_le_left hXn hfac hC hN hX3
  exact hX2.to_le hPX

end Abstract

section Config

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

omit [Finite G] in
theorem relIndex_pCoreOf_eq_card_quot (L : Subgroup G) :
    (pCoreOf 2 L).relIndex L = Nat.card (OTwoQuot L) := by
  have h3 : (pCoreOf 2 L).subgroupOf L = CFSG.Open.pCore 2 ↥L := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  show ((pCoreOf 2 L).subgroupOf L).index = _
  rw [h3, Subgroup.index]

theorem twoThree_Y153 (h1 : Case157One T Mc M) : TwoThree (Y153 Mc M) := by
  obtain ⟨e⟩ := h1.2
  refine twoThree_of_relIndex (n := 9) (Or.inr rfl) ?_
  rw [relIndex_pCoreOf_eq_card_quot, Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd]
  simp [Nat.card_eq_fintype_card]

theorem twoThree_M153 (c : Ctx153 G T Mc M V₁ V₂ t) (h1 : Case157One T Mc M)
    (hM : M = Y153 Mc M ⊔ T) : TwoThree M := by
  have hTM : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
    c.hyp.T_le.trans (le_normalizer_Y153 Mc M)
  have hT : TwoThree T := twoThree_of_isPGroup c.hyp.qtfe.sylow.1
  rw [hM]
  exact TwoThree.sup hTM (twoThree_Y153 h1) hT

theorem twoThree_GE153 (c : Ctx153 G T Mc M V₁ V₂ t) (r67 : Res15367 T Mc M V₁ V₂ E) :
    TwoThree (Subgroup.normalizer (E : Set G)) := by
  obtain ⟨eY⟩ := r67.YE_quot
  obtain ⟨eX⟩ := r67.XE_quot
  have hY : TwoThree (YE153 Mc M E) :=
    twoThree_of_relIndex (n := 3) (Or.inl rfl) (relIndex_pCoreOf_eq_three' eY)
  have hX : TwoThree (XE153 E) :=
    twoThree_of_relIndex (n := 3) (Or.inl rfl) (relIndex_pCoreOf_eq_three' eX)
  have hT : TwoThree (TE153 T E) :=
    twoThree_of_isPGroup (c.hyp.qtfe.sylow.1.to_le inf_le_left)
  have hXN : XE153 E ≤ Subgroup.normalizer (YE153 Mc M E : Set G) :=
    ((oTwoUpper_le _).trans (Subgroup.centralizer_le_normalizer _)).trans r67.YE_normal
  have hTN : TE153 T E ≤ Subgroup.normalizer ((YE153 Mc M E ⊔ XE153 E : Subgroup G) : Set G) :=
    le_normalizer_sup' (inf_le_right.trans r67.YE_normal) (inf_le_right.trans r67.XE_normal)
  rw [r67.GE_eq]
  exact TwoThree.sup hTN (TwoThree.sup hXN hY hX) hT

omit [Finite G] in
theorem twoThree_centralizer_FE153 (hGE : TwoThree (Subgroup.normalizer (E : Set G))) (s : G) :
    TwoThree (Subgroup.centralizer ((FE153 E s : Subgroup G) : Set G)) := by
  have hle : Subgroup.centralizer ((FE153 E s : Subgroup G) : Set G) ≤
      conjSubgroup (Subgroup.normalizer (E : Set G)) s := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    have hcen : s * x * s⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hf : s⁻¹ * e * s ∈ FE153 E s := by
        rw [mem_conjSubgroup_iff]
        have e1 : s * (s⁻¹ * e * s) * s⁻¹ = e := by group
        rw [e1]
        exact he
      have h := Subgroup.mem_centralizer_iff.mp hx _ hf
      calc e * (s * x * s⁻¹) = s * ((s⁻¹ * e * s) * x) * s⁻¹ := by group
        _ = s * (x * (s⁻¹ * e * s)) * s⁻¹ := by rw [h]
        _ = (s * x * s⁻¹) * e := by group
    exact Subgroup.centralizer_le_normalizer (E : Set G) hcen
  exact (hGE.conj s).mono hle

theorem normalizer_thompsonJ_TE_le_M (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) :
    Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) ≤ M ∧
      Y153 Mc M ⊔ T ≤ Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) := by
  classical
  have h := c.hyp
  have hRTE : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ TE153 T E := R_le_TE L
  have hJ : thompsonJ (TE153 T E) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    le_inf ((thompsonJ_le_self _).trans inf_le_left) (thompsonJ_TE_le_centralizer c L r66)
  have hJeq : thompsonJ (TE153 T E) =
      thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) := thompsonJ_eq_of_le hJ hRTE
  have hVΩ : VZ T M ≤ omegaOneCenterOf (thompsonJ (TE153 T E)) :=
    hJeq ▸ V_le_omegaOneCenter_thompsonJ h
  have hRn : Y153 Mc M ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) := by
    obtain ⟨he, hn⟩ := h.R153_Y153 h113 c.decomp
    rw [he] at hn
    exact hn
  have hYTJ : Y153 Mc M ⊔ T ≤ Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) := by
    rw [hJeq]
    exact hRn.trans (normalizer_le_normalizer_thompsonJ _)
  refine ⟨?_, hYTJ⟩
  have hU := h.lemma_15_3_7_unique h113
  have hVJ : VZ T M ≤ thompsonJ (TE153 T E) := fun v hv => A4.omegaOneCenterOf_le _ (hVΩ hv)
  have hJne : thompsonJ (TE153 T E) ≠ ⊥ := by
    intro hb
    have h1 : Nat.card (VZ T M) = 1 := by
      rw [Subgroup.card_eq_one]
      exact eq_bot_iff.mpr (hb ▸ hVJ)
    have := h.card_VZ
    omega
  have hJp : IsPGroup 2 ↥(thompsonJ (TE153 T E)) :=
    h.qtfe.sylow.1.to_le ((thompsonJ_le_self _).trans (inf_le_left : TE153 T E ≤ T))
  have hCO : thompsonJ (TE153 T E) ≤
      pCoreOf 2 (Subgroup.normalizer (thompsonJ (TE153 T E) : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hJp
  exact le_of_isUniqueM hU ⟨hYTJ, fun hb => hJne (le_bot_iff.mp (hb ▸ hCO))⟩

theorem exists_conj_mem_YF153 (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) {z f : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hf : f ∈ FE153 E s) (hf1 : f ≠ 1) :
    ∃ y ∈ YF153 Mc M E s, f = y * z * y⁻¹ := by
  have hsT : s ∈ T := gl.s_mem.1
  have hef : s * f * s⁻¹ ∈ E := mem_conjSubgroup_iff.mp hf
  have h1 : s * f * s⁻¹ ≠ 1 := by
    intro h
    apply hf1
    have e1 : f = s⁻¹ * (s * f * s⁻¹) * s := by group
    rw [e1, h]
    group
  obtain ⟨a, ha, hae⟩ := exists_conj_mem_YE153B c L r66 hz hz1 hef h1
  have hszc : z * s = s * z :=
    Subgroup.mem_centralizer_iff.mp (c.hyp.T_le_centralizer_Z hsT) z hz
  have hsz : s⁻¹ * z * s = z := by
    calc s⁻¹ * z * s = s⁻¹ * (z * s) := by group
      _ = s⁻¹ * (s * z) := by rw [hszc]
      _ = z := by group
  refine ⟨s⁻¹ * a * s, ?_, ?_⟩
  · rw [mem_conjSubgroup_iff]
    have : s * (s⁻¹ * a * s) * s⁻¹ = a := by group
    rw [this]
    exact ha
  · calc f = s⁻¹ * (s * f * s⁻¹) * s := by group
      _ = s⁻¹ * (a * z * a⁻¹) * s := by rw [hae]
      _ = (s⁻¹ * a * s) * (s⁻¹ * z * s) * (s⁻¹ * a * s)⁻¹ := by group
      _ = (s⁻¹ * a * s) * z * (s⁻¹ * a * s)⁻¹ := by rw [hsz]

end Config

section PFacts

variable {G : Type} [Group G] [Finite G]

abbrev oThreePrimeCore (D : Subgroup G) : Subgroup G := (CFSG.pPrimeCore 3 ↥D).map D.subtype

omit [Finite G] in
theorem oThreePrimeCore_le (D : Subgroup G) : oThreePrimeCore D ≤ D := Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_normalizer_oThreePrimeCore (D : Subgroup G) :
    D ≤ Subgroup.normalizer (oThreePrimeCore D : Set G) := by
  have hnorm : ((oThreePrimeCore D).subgroupOf D).Normal := by
    have : (oThreePrimeCore D).subgroupOf D = CFSG.pPrimeCore 3 ↥D := by
      unfold Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
    rw [this]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (oThreePrimeCore_le D)).mp hnorm

theorem not_three_dvd_card_oThreePrimeCore (D : Subgroup G) : ¬ 3 ∣ Nat.card (oThreePrimeCore D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥D)
  rw [Subgroup.card_map_of_injective D.subtype_injective]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h

theorem isSolvable_oThreePrimeCore {D G₁ G₂ : Subgroup G} (h : F6.IsGoldschmidtTripleIn D G₁ G₂) :
    Group.IsSolvable ↥(oThreePrimeCore D) := by
  have hs := h.isSolvable_pPrimeCore
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (CFSG.pPrimeCore 3 ↥D) D.subtype
      D.subtype_injective).symm.toMonoidHom)
    (Subgroup.equivMapOfInjective (CFSG.pPrimeCore 3 ↥D) D.subtype D.subtype_injective).symm.injective

theorem isSylowTwoOf_pCoreOf_oThreePrimeCore {D G₁ G₂ : Subgroup G}
    (h : F6.IsGoldschmidtTripleIn D G₁ G₂) : IsSylowTwoOf (pCoreOf 2 D) (oThreePrimeCore D) := by
  have hS := h.isSylowTwoOf_pCore_pPrimeCore
  refine ⟨Subgroup.map_mono hS.1, hS.2.1.map _, ?_⟩
  have e : (pCoreOf 2 D).relIndex (oThreePrimeCore D) =
      (Open.pCore 2 ↥D).relIndex (CFSG.pPrimeCore 3 ↥D) :=
    Subgroup.relIndex_map_map_of_injective (f := D.subtype) _ _ D.subtype_injective
  have hS2 : ¬ 2 ∣ (Open.pCore 2 ↥D).relIndex (CFSG.pPrimeCore 3 ↥D) := hS.2.2
  show ¬ 2 ∣ (pCoreOf 2 D).relIndex (oThreePrimeCore D)
  rw [e]
  exact hS2

end PFacts

section Final

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem pCore_eq_of (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (r49 : Res15349 T Mc M V₁) (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (hV : VZ T M ≤ pCoreOf 2 (G0_153 T Mc M E s))
    (htriple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E)) :
    pCoreOf 2 (G0_153 T Mc M E s) =
      (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map (G0_153 T Mc M E s).subtype := by
  have h := c.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup G := G0_153 T Mc M E s with hD
  have hPD : oThreePrimeCore D ≤ D := oThreePrimeCore_le D
  have hDP := le_normalizer_oThreePrimeCore D
  have hQP : pCoreOf 2 D ≤ oThreePrimeCore D := (isSylowTwoOf_pCoreOf_oThreePrimeCore htriple).1
  have hTED : TE153 T E ≤ D := le_sup_right.trans le_sup_left
  have hTEsyl : IsSylowTwoOf (TE153 T E) D := by
    have := htriple.2.2.2
    rwa [G1_inf_G2 c L r66 r67 gl] at this
  have hQD : pCoreOf 2 D ≤ D := pCoreOf_le 2 D
  have hQTE : pCoreOf 2 D ≤ TE153 T E :=
    A4.le_of_normal_of_isSylowTwoOf hTEsyl hQD
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr (le_normalizer_pCoreOf 2 D))
      (pCoreOf_isPGroup 2 D)
  have hTE2 : IsPGroup 2 ↥(TE153 T E) := h.qtfe.sylow.1.to_le inf_le_left
  have hCT : Subgroup.centralizer (VZ T M : Set G) ≤ T := by
    rw [← r67.R_eq]
    exact inf_le_left
  have hCV : IsPGroup 2 ↥(Subgroup.centralizer (VZ T M : Set G)) := h.qtfe.sylow.1.to_le hCT
  obtain ⟨hNJM, hYTJ⟩ := normalizer_thompsonJ_TE_le_M h113 c L r66
  have hYJ : YF153 Mc M E s ≤ Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) :=
    (YF_le_Y c gl).trans (le_sup_left.trans hYTJ)
  have hYD : YF153 Mc M E s ≤ D := le_sup_left.trans le_sup_left
  have hZQ : quasithinOmegaOneCenter T ≤ pCoreOf 2 D :=
    (le_conjClosure (quasithinOmegaOneCenter T) M).trans hV
  have hZc : ∀ z ∈ quasithinOmegaOneCenter T, ∀ u ∈ TE153 T E, z * u = u * z := by
    intro z hz u hu
    exact (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hz).2 u hu.1).symm
  have hZ2 : ∀ z ∈ quasithinOmegaOneCenter T, z * z = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := ↥(quasithinOmegaOneCenter T)) (x := ⟨z, hz⟩)
    rw [h.lemma_15_3_2_two.2] at this
    have := congrArg Subtype.val this
    simpa [pow_two] using this
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.qtfe.omegaOneCenter_ne_bot
  have hz₀1' : z₀ ≠ 1 := fun h1 => hz₀1 (Subtype.ext h1)
  have hF : ∀ f ∈ FE153 E s, f ≠ 1 →
      ∃ y ∈ YF153 Mc M E s, ∃ z ∈ quasithinOmegaOneCenter T, f = y * z * y⁻¹ := by
    intro f hf hf1
    obtain ⟨y, hy, hfy⟩ := exists_conj_mem_YF153 c L r66 gl hz₀ hz₀1' hf hf1
    exact ⟨y, hy, z₀, hz₀, hfy⟩
  have hCF := twoThree_centralizer_FE153 (twoThree_GE153 c r67) s
  have hNJ : TwoThree (Subgroup.normalizer (thompsonJ (TE153 T E) : Set G)) :=
    (twoThree_M153 c r49.case_one r67.M_eq).mono hNJM
  have hP2 : IsPGroup 2 ↥(oThreePrimeCore D) :=
    isPGroup_two_of_thompson_factor hPD hDP (not_three_dvd_card_oThreePrimeCore D)
      (isSolvable_oThreePrimeCore htriple) hQP (isSylowTwoOf_pCoreOf_oThreePrimeCore htriple)
      (le_normalizer_pCoreOf 2 D) (pCoreOf_isPGroup 2 D) hTED hTE2 hQTE hV hCV hYD hYJ hZQ hZc hZ2
      hF hCF hNJ
  exact le_antisymm hQP (le_pCoreOf_of_le_normalizer 2 hPD hDP hP2)

end Final

end C1Pack153

@[expose] def Stage15368Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E →
        Res15367 T Mc M V₁ V₂ E → GoldLine153 T V₁ E s →
          G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G) →
          VZ T M ≤ pCoreOf 2 (G0_153 T Mc M E s) →
          (∀ M₀ : Subgroup G, InM (G0_153 T Mc M E s) M₀ → IsSylowTwoOf (TE153 T E) M₀) →
          F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E) →
            pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G)

theorem stage15368Rest2_of_two (h113 : StageLemma14113) (i : Stage15368Two) : Stage15368Rest2 := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl h1 hV hSyl htriple
  exact ⟨i G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl h1 hV hSyl htriple,
    C1Pack153.pCore_eq_of h113 c r49 L r66 r67 gl hV htriple⟩

end CFSG.Quasithin
