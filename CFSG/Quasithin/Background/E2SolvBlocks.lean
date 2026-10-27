module

public import CFSG.Quasithin.Background.E2Frattini
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.Background.A1cA131

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

structure Blocks (H : Subgroup G) (𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))) : Prop where
  hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn (autI hV H))) 𝓗
  sub : I ⊆ 𝓗
  eq : autI hV (thompsonJ H) = ⨆ L ∈ I, L
  syl : ∀ L ∈ I, ∀ S, IsSylowTwoOf S L → S ∈ offenderImages hV H

theorem exists_blocks {H T : Subgroup G} (hred : IsTwoReducedIn H V)
    (hsolv : Group.IsSolvable H) (hT : IsSylowTwoOf T H)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∃ 𝓗 I, Blocks hV H 𝓗 I := by
  have hVH : V ≤ H := hred.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h)
  obtain ⟨-, hstable, hNeq, -⟩ := B2_7_of_not_le hV hVH hHN hJH
  have hsolvX := isSolvable_autI hV hHN hsolv
  have hO2 := fun Q (hQ : Q ≤ autI hV H) hQn hQ2 => eq_bot_of_normal_isPGroup hV hred hQ hQn hQ2
  have hJX := B1.closure_transvectionsIn_le (autI hV H)
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn (autI hV H))) :=
    B1.solvable_of_le hJX hsolvX
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO2
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn (autI hV H)))) =
      Subgroup.closure (transvectionsIn (autI hV H)) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hW hsolvJ hOJ hcl
  obtain ⟨I, hI𝓗, hJPeq, hsylI, -⟩ := hb.stable_decomposition hW hsolvX hO2 hstable
  exact ⟨𝓗, I, hb, hI𝓗, hNeq.trans hJPeq, hsylI⟩

namespace Blocks

variable {hV} {H : Subgroup G} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

omit [Finite G] in
theorem le_thompsonJ (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    L ≤ autI hV (thompsonJ H) := by
  rw [B.eq]
  exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ I) => K) L hL
    le_rfl

omit [Finite G] in
theorem le_autI (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    L ≤ autI hV H :=
  (B.le_thompsonJ hL).trans (autI_mono hV (thompsonJ_le_self H))

omit [Finite G] in
theorem card_eq (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    Nat.card L = 6 :=
  B.hb.card_eq L (B.sub hL)

omit [Finite G] in
theorem comm (B : Blocks hV H 𝓗 I) {L L' : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I)
    (hL' : L' ∈ I) (hne : L ≠ L') {a b : MulAut (IntMod V hV)} (ha : a ∈ L) (hb : b ∈ L') :
    a * b = b * a :=
  B.hb.comm L (B.sub hL) L' (B.sub hL') hne a ha b hb

omit [Finite G] in
theorem le_normalizer (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    autI hV (thompsonJ H) ≤
      Subgroup.normalizer ((L : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
  rw [B.eq]
  refine iSup₂_le fun L' hL' => ?_
  by_cases hLL : L' = L
  · rw [hLL]
    exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer
      ((L : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))))
    intro a ha
    exact Subgroup.mem_centralizer_iff.2 fun b hb' => (B.comm hL' hL hLL ha hb').symm

omit [Finite G] in
theorem inf_biSup_ne (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥ := by
  refine le_bot_iff.1 ?_
  calc L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' ≤ L ⊓ ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L), L' :=
        inf_le_inf_left L (iSup₂_mono' fun L' hL' => ⟨L', B.sub hL', le_rfl⟩)
    _ = ⊥ := B.hb.inf_biSup_ne_eq_bot (B.sub hL)

end Blocks

section MinPar

variable {H T M : Subgroup G} {hV} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

omit [Finite G] in
theorem commutator_ne_bot (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ⁅V, thompsonJ T⁆ ≠ ⊥ := by
  intro hc
  apply hJ
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  exact Subgroup.le_centralizer_iff.mp hc

theorem twoResidual_le_thompsonJ (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : twoResidual H ≤ thompsonJ H := by
  rw [h.thompsonJ_eq_sup hred (commutator_ne_bot hJ)]
  exact le_sup_left

omit [Finite G] in
theorem not_le_centralizer (h : MinParabolic H T M)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ¬ H ≤ Subgroup.centralizer (V : Set G) :=
  fun hle => hJ ((thompsonJ_le_self T).trans (h.isSylow.1.trans hle))

theorem autI_twoResidual_ne_bot (h : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    autI hV (twoResidual H) ≠ ⊥ := by
  rw [Ne, autI_eq_bot_iff hV ((twoResidual_le H).trans hred.2.1)]
  exact MinParabolic.not_twoResidual_le_centralizer hred (not_le_centralizer h hJ)

theorem mem_autI_twoResidual_of_odd {x : MulAut (IntMod V hV)} (hx : x ∈ autI hV H)
    (hodd : Odd (orderOf x)) : x ∈ autI hV (twoResidual H) := by
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hx
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H g hgH
  refine mem_of_odd_orderOf_of_pow_mem hodd (k := k) ?_
  rw [← map_pow]
  exact convI_mem_autI hV hk (Subgroup.pow_mem _ g.2 _)

theorem Blocks.isPGroup_autI_twoResidual (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    IsPGroup 3 (autI hV (twoResidual H)) := by
  obtain ⟨p, hpp, hp2, hpow⟩ := h.exists_prime_pow_mem_pCoreOf hsolv
  have : Fact p.Prime := ⟨hpp⟩
  have hKp : IsPGroup p (autI hV (twoResidual H)) := by
    intro x
    obtain ⟨g, hgK, hgx⟩ := (mem_autI hV).1 x.2
    obtain ⟨a, ha⟩ := hpow g hgK
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hgx, ← map_pow, convI_eq_one_iff]
    exact MinParabolic.pCoreOf_le_centralizer hred (by simpa using ha)
  have hne := autI_twoResidual_ne_bot (hV := hV) h hred hJ
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨b, hb⟩ := hKp x
  have hord : orderOf x ∣ p ^ b := orderOf_dvd_of_pow_eq_one hb
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hpp).mp hord
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hc))
  have hxJ : (x : MulAut (IntMod V hV)) ∈ ⨆ L ∈ I, L := by
    rw [← B.eq]
    exact autI_mono hV (twoResidual_le_thompsonJ h hred hJ) x.2
  have hcard : Nat.card ↥(⨆ L ∈ I, L) = 6 ^ I.card := by
    have h1 := B.hb.card_biSup_eq_prod (fun L => L) (fun L _ => le_rfl) I B.sub
    beta_reduce at h1
    rw [h1, Finset.prod_congr rfl (fun L hL => B.hb.card_eq L (B.sub hL))]
    simp
  have hdvd : orderOf (x : MulAut (IntMod V hV)) ∣ 6 ^ I.card := by
    have := orderOf_dvd_natCard (⟨x, hxJ⟩ : ↥(⨆ L ∈ I, L))
    rwa [Subgroup.orderOf_mk, hcard] at this
  rw [Subgroup.orderOf_coe, hc] at hdvd
  have hp6 : p ∣ 6 := hpp.dvd_of_dvd_pow ((dvd_pow_self p hc0).trans hdvd)
  have hp3 : p = 3 := by
    have h6 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h6] at hp6
    rcases (Nat.Prime.dvd_mul hpp).mp hp6 with h2 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h3
  rw [← hp3]
  exact hKp

theorem Blocks.exists_orderOf_eq_three (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) : ∃ f ∈ L, f ∈ autI hV (twoResidual H) ∧ orderOf f = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 (by rw [B.card_eq hL]; norm_num)
  refine ⟨y, y.2, mem_autI_twoResidual_of_odd (B.le_autI hL y.2) ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hy]
    decide
  · rw [Subgroup.orderOf_coe, hy]

omit [Finite G] in
theorem conjAut_autI_thompsonJ {g : MulAut (IntMod V hV)} (hg : g ∈ autI hV H) :
    B1.conjAut g (autI hV (thompsonJ H)) = autI hV (thompsonJ H) := by
  obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hg
  have hyN : (y : G) ∈ Subgroup.normalizer (V : Set G) := y.2
  rw [conjAut_eq_map, autI_cjSub hV hyN (thompsonJ H),
    cjSub_eq_of_mem_normalizer (normalizer_le_normalizer_thompsonJ H (Subgroup.le_normalizer hy))]

theorem Blocks.isSylowTwoOf_inf (B : Blocks hV H 𝓗 I) (hred : IsTwoReducedIn H V)
    (hT : IsSylowTwoOf T H) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    IsSylowTwoOf (autI hV T ⊓ L) L := by
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hTs := isSylowTwoOf_autI hV hHN hT
  have hNX : autI hV (thompsonJ H) ≤ autI hV H := autI_mono hV (thompsonJ_le_self H)
  have hTsN : autI hV T ≤ Subgroup.normalizer
      ((autI hV (thompsonJ H) : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
    intro t ht
    refine Subgroup.mem_normalizer_iff''.2 fun x => ?_
    rw [← B1.mem_conjAut, conjAut_autI_thompsonJ (autI_mono hV hT.1 ht)]
  have hTN : IsSylowTwoOf (autI hV T ⊓ autI hV (thompsonJ H)) (autI hV (thompsonJ H)) :=
    ⟨inf_le_right, (isPGroup_autI hV hT.2.1 (hT.1.trans hHN)).to_le inf_le_left,
      not_two_dvd_relIndex_inf_of_normalizer hTs.1 hNX hTs.2.2 hTsN⟩
  have h := not_two_dvd_relIndex_inf_of_normalizer
    (S := autI hV T ⊓ autI hV (thompsonJ H)) (D := L) (K := autI hV (thompsonJ H)) hTN.1
    (B.le_thompsonJ hL) hTN.2.2 (inf_le_right.trans (B.le_normalizer hL))
  have heq : (autI hV T ⊓ autI hV (thompsonJ H)) ⊓ L = autI hV T ⊓ L := by
    rw [inf_assoc, inf_eq_right.2 (B.le_thompsonJ hL)]
  rw [heq] at h
  exact ⟨inf_le_right, (isPGroup_autI hV hT.2.1 (hT.1.trans hHN)).to_le inf_le_left, h⟩

theorem Blocks.exists_orderOf_eq_two (B : Blocks hV H 𝓗 I) (hred : IsTwoReducedIn H V)
    (hT : IsSylowTwoOf T H) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    ∃ t ∈ L, t ∈ autI hV T ∧ t ∈ autI hV (thompsonJ T) ∧ orderOf t = 2 := by
  have hS := B.isSylowTwoOf_inf hred hT hL
  have hcard : Nat.card ↥(autI hV T ⊓ L) = 2 := by
    have h := Subgroup.relIndex_mul_card (autI hV T ⊓ L) L
    rw [inf_eq_left.2 (inf_le_right : autI hV T ⊓ L ≤ L), B.card_eq hL] at h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS.2.1
    have hodd : ¬ 2 ∣ (autI hV T ⊓ L).relIndex L := hS.2.2
    rw [hk] at h ⊢
    rcases k with _ | _ | k
    · exfalso
      apply hodd
      have : (autI hV T ⊓ L).relIndex L = 6 := by simpa using h
      rw [this]
      norm_num
    · norm_num
    · exfalso
      have h4 : 4 * ((autI hV T ⊓ L).relIndex L * 2 ^ k) = 6 := by
        rw [← h]
        ring
      omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autI hV T ⊓ L)) 2 (by rw [hcard])
  have hSJ : autI hV T ⊓ L ≤ autI hV (thompsonJ T) :=
    offenderImages_le_autI_thompsonJ hV hred.2.1 hT (B.syl L hL _ hS) inf_le_left
  exact ⟨y, y.2.2, y.2.1, hSJ y.2, by rw [Subgroup.orderOf_coe, hy]⟩

theorem Blocks.not_comm (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) : ¬ ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
  intro hc
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨t₀, ht₀⟩ := B.hb.exists_transvection (B.sub hL)
  have htsq : ∀ t ∈ transvectionsIn L, t ^ 2 = 1 := fun t ht => by
    obtain ⟨-, ht1, w, htw⟩ := ht
    rw [pow_two]
    exact B1.tv_sq hW htw ht1
  have heq : ∀ t ∈ transvectionsIn L, t = t₀ := by
    intro t ht
    by_contra hne
    exact IsTransvectionBlocks.not_commuting_involutions (B.card_eq hL) ht.1 ht₀.1 (htsq t ht)
      (htsq t₀ ht₀) ht.2.1 ht₀.2.1 hne (hc t ht.1 t₀ ht₀.1)
  have hle : L ≤ Subgroup.zpowers t₀ := by
    rw [← B.hb.closure_eq L (B.sub hL), Subgroup.closure_le]
    intro t ht
    rw [heq t ht]
    exact Subgroup.mem_zpowers t₀
  have h1 := Subgroup.card_le_of_le hle
  rw [B.card_eq hL, Nat.card_zpowers, orderOf_eq_prime (htsq t₀ ht₀) ht₀.2.1] at h1
  omega

theorem Blocks.mul_ne_mul (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) {t f : MulAut (IntMod V hV)} (ht : t ∈ L) (hf : f ∈ L) (ht2 : orderOf t = 2)
    (hf3 : orderOf f = 3) : t * f ≠ f * t := by
  intro hc
  apply B.not_comm hL
  have hord : orderOf (t * f) = 6 := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hc (by rw [ht2, hf3]; norm_num), ht2, hf3]
  have hZL : Subgroup.zpowers (t * f) ≤ L := Subgroup.zpowers_le.2 (L.mul_mem ht hf)
  have hZeq : Subgroup.zpowers (t * f) = L :=
    Subgroup.eq_of_le_of_card_ge hZL (by rw [Nat.card_zpowers, hord, B.card_eq hL])
  intro a ha b hb
  rw [← hZeq] at ha hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact (Commute.zpow_zpow_self (t * f) i j).eq

omit [Finite G] in
theorem mem_normalizer_of_conjAut_le {g : MulAut (IntMod V hV)}
    {Y : Subgroup (MulAut (IntMod V hV))} (h1 : B1.conjAut g Y ≤ Y)
    (h2 : B1.conjAut g⁻¹ Y ≤ Y) : g ∈ Subgroup.normalizer (Y : Set (MulAut (IntMod V hV))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 (B1.mem_conjAut.mpr (by simpa [mul_assoc] using hx))
  · intro hx
    exact h2 (B1.mem_conjAut.mpr (by simpa [mul_assoc] using hx))

theorem Blocks.conjAut_mem (B : Blocks hV H 𝓗 I) {g : MulAut (IntMod V hV)} (hg : g ∈ autI hV H)
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) : B1.conjAut g L ∈ I := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hN' : B1.conjAut g (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, L := by
    rw [← B.eq, conjAut_autI_thompsonJ hg]
  exact B.hb.conjAut_mem hW B.sub hg hN' hL

theorem Blocks.conjAut_eq_of_mem_twoResidual (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    {k : MulAut (IntMod V hV)} (hk : k ∈ autI hV (twoResidual H))
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) : B1.conjAut k L = L := by
  have hkN := B.le_normalizer hL (autI_mono hV (twoResidual_le_thompsonJ h hred hJ) hk)
  rw [conjAut_eq_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hkN

theorem odd_card_autI_kerIn (h : MinParabolic H T M) (hred : IsTwoReducedIn H V) :
    Odd (Nat.card (autI hV (kerIn M H))) := by
  have hJN : kerIn M H ≤ Subgroup.normalizer (V : Set G) := h.kerIn_le_H.trans hred.2.1
  have hQJ : pCoreOf 2 H ≤ kerIn M H ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf h.pCoreOf_le_kerIn (MinParabolic.pCoreOf_le_centralizer hred)
  have hsyl := h.isSylowTwoOf_pCoreOf_kerIn
  have e1 := card_autI_mul_card_inf hV hJN
  have e2 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) (kerIn M H ⊓ Subgroup.centralizer
    (V : Set G)) (kerIn M H) hQJ inf_le_left
  have e3 := Subgroup.relIndex_mul_card (kerIn M H ⊓ Subgroup.centralizer (V : Set G)) (kerIn M H)
  rw [inf_eq_left.2 (inf_le_left : kerIn M H ⊓ Subgroup.centralizer (V : Set G) ≤ kerIn M H)]
    at e3
  have hpos : 0 < Nat.card ↥(kerIn M H ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have hrel : (kerIn M H ⊓ Subgroup.centralizer (V : Set G)).relIndex (kerIn M H) =
      Nat.card (autI hV (kerIn M H)) :=
    Nat.eq_of_mul_eq_mul_right hpos (e3.trans e1.symm)
  have hodd : ¬ 2 ∣ (pCoreOf 2 H).relIndex (kerIn M H) := hsyl.2.2
  rw [← e2, hrel] at hodd
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun hd => hodd (hd.mul_left _))

theorem Blocks.transitive (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    {L₀ L₁ : Subgroup (MulAut (IntMod V hV))} (hL₀ : L₀ ∈ I) (hL₁ : L₁ ∈ I) :
    ∃ t ∈ autI hV T, B1.conjAut t L₀ = L₁ := by
  classical
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := h.isSylow.1.trans hHN
  have hKN : twoResidual H ≤ Subgroup.normalizer (V : Set G) := (twoResidual_le H).trans hHN
  by_contra hcon
  set 𝓞 := I.filter (fun L => ∃ t ∈ autI hV T, B1.conjAut t L₀ = L) with h𝓞
  set Y : Subgroup (MulAut (IntMod V hV)) := ⨆ L ∈ 𝓞, L with hY
  have h𝓞I : 𝓞 ⊆ I := Finset.filter_subset _ _
  have hL₀𝓞 : L₀ ∈ 𝓞 := Finset.mem_filter.2 ⟨hL₀, 1, Subgroup.one_mem _, by
    ext x
    simp [B1.mem_conjAut]⟩
  have hL₁𝓞 : L₁ ∉ 𝓞 := fun hm => hcon (Finset.mem_filter.1 hm).2
  have hYH : Y ≤ autI hV H := iSup₂_le fun L hL => B.le_autI (h𝓞I hL)
  have hTY : ∀ t ∈ autI hV T, B1.conjAut t Y ≤ Y := by
    intro t ht
    rw [conjAut_eq_map, hY, Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    obtain ⟨hLI, t', ht', hL'⟩ := Finset.mem_filter.1 hL
    have hmem : B1.conjAut t L ∈ 𝓞 := by
      refine Finset.mem_filter.2 ⟨B.conjAut_mem (autI_mono hV h.isSylow.1 ht) hLI,
        t * t', Subgroup.mul_mem _ ht ht', ?_⟩
      rw [← hL', conjAut_eq_map, conjAut_eq_map, conjAut_eq_map, Subgroup.map_map]
      rfl
    have := le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ 𝓞) => K)
      (B1.conjAut t L) hmem le_rfl
    rw [conjAut_eq_map] at this
    exact this
  have hKY : ∀ k ∈ autI hV (twoResidual H), B1.conjAut k Y ≤ Y := by
    intro k hk
    rw [conjAut_eq_map, hY, Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    have := B.conjAut_eq_of_mem_twoResidual h hred hJ hk (h𝓞I hL)
    rw [conjAut_eq_map] at this
    rw [this]
    exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ 𝓞) => K) L hL
      le_rfl
  have hYn : autI hV H ≤ Subgroup.normalizer
      ((Y : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
    have hH : autI hV H = autI hV T ⊔ autI hV (twoResidual H) := by
      rw [← autI_sup hV hTN hKN, sup_twoResidual_eq h.isSylow]
    rw [hH]
    refine sup_le (fun t ht => ?_) (fun k hk => ?_)
    · exact mem_normalizer_of_conjAut_le (hTY t ht) (hTY t⁻¹ (Subgroup.inv_mem _ ht))
    · exact mem_normalizer_of_conjAut_le (hKY k hk) (hKY k⁻¹ (Subgroup.inv_mem _ hk))
  set Y₀ := preI hV H hHN Y with hY₀
  have hY₀H : Y₀ ≤ H := preI_le hV
  have hY₀Y : autI hV Y₀ = Y := autI_preI hV hYH
  have hY₀n : H ≤ Subgroup.normalizer (Y₀ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ H, ∀ x ∈ Y₀, g * x * g⁻¹ ∈ Y₀ := by
      intro g hg x hx
      obtain ⟨hxH, hxY⟩ := (mem_preI hV).1 hx
      have hgxH : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg)
      refine (mem_preI hV).2 ⟨hgxH, ?_⟩
      have hgY := hYn (convI_mem_autI hV hg (hHN hg))
      have h1 := (Subgroup.mem_normalizer_iff.mp hgY _).mp hxY
      have h2 : convHom hV H hHN ⟨g * x * g⁻¹, hgxH⟩ =
          convHom hV H hHN ⟨g, hg⟩ * convHom hV H hHN ⟨x, hxH⟩ * (convHom hV H hHN ⟨g, hg⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [h2]
      exact h1
    intro x
    refine ⟨key g hg x, fun hx => ?_⟩
    have := key g⁻¹ (H.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  rcases h.le_kerIn_or_twoResidual_le hY₀H hY₀n with hJ₀ | hK₀
  ·
    have hYJ : Y ≤ autI hV (kerIn M H) := hY₀Y ▸ autI_mono hV hJ₀
    have hL₀Y : L₀ ≤ autI hV (kerIn M H) :=
      (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ 𝓞) => K) L₀
        hL₀𝓞 le_rfl).trans hYJ
    have hdvd := Subgroup.card_dvd_of_le hL₀Y
    rw [B.card_eq hL₀] at hdvd
    have hodd := odd_card_autI_kerIn (hV := hV) h hred
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 6).trans hdvd))
  ·
    have hKY' : autI hV (twoResidual H) ≤ Y := hY₀Y ▸ autI_mono hV hK₀
    obtain ⟨f, hfL, hfK, hf3⟩ := B.exists_orderOf_eq_three hL₁
    have hfY : f ∈ Y := hKY' hfK
    have hYle : Y ≤ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L₁), L' := by
      refine iSup₂_le fun L hL => ?_
      have hLne : L ≠ L₁ := fun he => hL₁𝓞 (he ▸ hL)
      exact le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ I) =>
        ⨆ (_ : K ≠ L₁), K) L (h𝓞I hL) (le_iSup (fun _ : L ≠ L₁ => L) hLne)
    have hf1 : f ∈ L₁ ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L₁), L' := ⟨hfL, hYle hfY⟩
    rw [B.inf_biSup_ne hL₁, Subgroup.mem_bot] at hf1
    rw [hf1, orderOf_one] at hf3
    exact absurd hf3 (by norm_num)

omit [Finite G] in
theorem Blocks.eq_one_of_mem_of_mem (B : Blocks hV H 𝓗 I) {L L' : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) (hL' : L' ∈ I) (hne : L' ≠ L) {x : MulAut (IntMod V hV)} (hx : x ∈ L)
    (hx' : x ∈ L') : x = 1 := by
  have hmem : x ∈ L ⊓ ⨆ L'' ∈ I, ⨆ (_ : L'' ≠ L), L'' :=
    ⟨hx, le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ I) =>
      ⨆ (_ : K ≠ L), K) L' hL' (le_iSup (fun _ : L' ≠ L => L') hne) hx'⟩
  rw [B.inf_biSup_ne hL, Subgroup.mem_bot] at hmem
  exact hmem

theorem Blocks.card_le_two (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : I.card ≤ 2 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨L₁, hL₁, L₂, hL₂, L₃, hL₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  set X := autI hV H with hX
  have hmemX : ∀ g : H, convHom hV H hHN g ∈ X := fun g => by
    rw [hX, ← range_convHom hV H hHN]
    exact ⟨g, rfl⟩
  let φ : H →* X := (convHom hV H hHN).codRestrict X hmemX
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [hX, ← range_convHom hV H hHN] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKX : autI hV (twoResidual H) ≤ X := autI_mono hV (twoResidual_le H)
  set K3 : Subgroup X := (autI hV (twoResidual H)).subgroupOf X with hK3
  have hK3p : IsPGroup 3 K3 :=
    (B.isPGroup_autI_twoResidual h hsolv hred hJ).of_equiv (Subgroup.subgroupOfEquivOfLe hKX).symm
  have hK3n : K3.Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [hK3, Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨a, haK, hak⟩ := (mem_autI hV).1 hk
    obtain ⟨b, hbH, hbg⟩ := (mem_autI hV).1 g.2
    have hbab : ((b * a * b⁻¹ : Subgroup.normalizer (V : Set G)) : G) ∈ twoResidual H := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H hbH) a).mp haK
    refine (mem_autI hV).2 ⟨b * a * b⁻¹, hbab, ?_⟩
    simp only [map_mul, map_inv, hak, hbg, Subgroup.coe_mul, Subgroup.coe_inv]
  have hK3le : K3 ≤ CFSG.Open.pCore 3 X := CFSG.LieType.BorelTits.le_pCore 3 hK3n hK3p
  have hsolvX : Group.IsSolvable X := isSolvable_autI hV hHN hsolv
  have hO2X : CFSG.Open.pCore 2 X = ⊥ := by
    set P2 := CFSG.Open.pCore 2 X with hP2
    have hP2n : P2.Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hP2p : IsPGroup 2 P2 := CFSG.LieType.BorelTits.pCore_isPGroup 2
    have h1 : P2.map X.subtype = ⊥ := by
      refine eq_bot_of_normal_isPGroup hV hred (Subgroup.map_subtype_le P2) ?_
        (hP2p.map X.subtype)
      have : (P2.map X.subtype).subgroupOf X = P2 :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective P2
      rw [this]
      exact hP2n
    exact (Subgroup.map_eq_bot_iff_of_injective P2 X.subtype_injective).mp h1
  have h2P : ∀ y : X, ∃ k : ℕ, y ^ 2 ^ k ∈ CFSG.Open.pCore 3 X := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hy
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H g hgH
    refine ⟨k, hK3le ?_⟩
    rw [hK3, Subgroup.mem_subgroupOf, Subgroup.coe_pow, ← map_pow]
    exact convI_mem_autI hV hk _
  have hF := centralizer_pCore_le Nat.prime_three h2P hO2X hsolvX
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 2 := by
    rw [pRank_top_subtype]
    exact hSQT
  have hA := (A1c.A131Concl_of_surjective (p := 3) (by norm_num) hF _ H φ hφ rfl hrk).1
  obtain ⟨t, htL, -, -, ht2⟩ := B.exists_orderOf_eq_two hred h.isSylow hL₁
  obtain ⟨f₂, hf₂L, hf₂K, hf₂3⟩ := B.exists_orderOf_eq_three hL₂
  obtain ⟨f₃, hf₃L, hf₃K, hf₃3⟩ := B.exists_orderOf_eq_three hL₃
  set t' : X := ⟨t, B.le_autI hL₁ htL⟩ with ht'
  have ht'2 : orderOf t' = 2 := by rw [ht', Subgroup.orderOf_mk, ht2]
  set T' : Subgroup X := Subgroup.zpowers t' with hT'
  have hT'p : IsPGroup 2 T' := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2, pow_one])
  have hT'1 : T' ≠ ⊥ := by
    intro he
    have h1 : t' ∈ T' := Subgroup.mem_zpowers t'
    rw [he, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at ht'2
    norm_num at ht'2
  have hcyc := hA T' hT'p hT'1
  set C := CFSG.Open.pCore 3 X ⊓ Subgroup.centralizer (T' : Set X) with hC
  have hmemC : ∀ (f : MulAut (IntMod V hV)) (L : Subgroup (MulAut (IntMod V hV))), L ∈ I →
      L ≠ L₁ → f ∈ L → f ∈ autI hV (twoResidual H) →
        ∃ hf : f ∈ X, (⟨f, hf⟩ : X) ∈ C := by
    intro f L hL hLL hfL hfK
    refine ⟨hKX hfK, Subgroup.mem_inf.mpr ⟨hK3le (Subgroup.mem_subgroupOf.mpr hfK), ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute t' ⟨f, hKX hfK⟩ := Subtype.ext (B.comm hL₁ hL hLL.symm htL hfL)
    exact (hc.zpow_left i).eq
  obtain ⟨hf₂X, hf₂C⟩ := hmemC f₂ L₂ hL₂ (Ne.symm h12) hf₂L hf₂K
  obtain ⟨hf₃X, hf₃C⟩ := hmemC f₃ L₃ hL₃ (Ne.symm h13) hf₃L hf₃K
  have : IsCyclic C := hcyc
  let : Fintype C := Fintype.ofFinite _
  set a : C := ⟨⟨f₂, hf₂X⟩, hf₂C⟩ with ha
  set b : C := ⟨⟨f₃, hf₃X⟩, hf₃C⟩ with hb
  have hinj : ∀ x y : C, ((x : X) : MulAut (IntMod V hV)) = ((y : X) : MulAut (IntMod V hV)) →
      x = y := fun x y hxy => Subtype.ext (Subtype.ext hxy)
  have hf₂1 : f₂ ≠ 1 := fun he => by rw [he, orderOf_one] at hf₂3; norm_num at hf₂3
  have hf₃1 : f₃ ≠ 1 := fun he => by rw [he, orderOf_one] at hf₃3; norm_num at hf₃3
  have hf₂sq : f₂ ^ 2 ≠ 1 := fun he => by
    have := orderOf_dvd_of_pow_eq_one he
    rw [hf₂3] at this
    norm_num at this
  have hf₂f₂ : f₂ ≠ f₂ ^ 2 := fun he => hf₂1 (by
    have : f₂ * 1 = f₂ * f₂ := by rw [mul_one, ← pow_two, ← he]
    exact (mul_left_cancel this).symm)
  have hf₃L₂ : ∀ y ∈ L₂, f₃ ≠ y := fun y hy he =>
    hf₃1 (B.eq_one_of_mem_of_mem hL₃ hL₂ h23 hf₃L (he ▸ hy))
  have hsub : ({1, a, a ^ 2, b} : Finset C) ⊆ Finset.univ.filter (fun x : C => x ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_pow 3
    · apply hinj
      simp [ha, ← hf₂3, pow_orderOf_eq_one]
    · apply hinj
      simp only [ha, Subgroup.coe_pow, Subgroup.coe_one]
      rw [← pow_mul, mul_comm, pow_mul, ← hf₂3, pow_orderOf_eq_one, one_pow]
    · apply hinj
      simp [hb, ← hf₃3, pow_orderOf_eq_one]
  have hcard4 : ({1, a, a ^ 2, b} : Finset C).card = 4 := by
    have h1a : (1 : C) ≠ a := fun he => hf₂1 (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he).symm
    have h1a2 : (1 : C) ≠ a ^ 2 := fun he => hf₂sq (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he).symm
    have h1b : (1 : C) ≠ b := fun he => hf₃1 (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he).symm
    have haa2 : a ≠ a ^ 2 := fun he => hf₂f₂ (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he)
    have hab : a ≠ b := fun he => hf₃L₂ f₂ hf₂L (congrArg (fun x : C =>
      ((x : X) : MulAut (IntMod V hV))) he).symm
    have ha2b : a ^ 2 ≠ b := fun he => hf₃L₂ (f₂ ^ 2) (L₂.pow_mem hf₂L 2) (congrArg
      (fun x : C => ((x : X) : MulAut (IntMod V hV))) he).symm
    rw [Finset.card_insert_of_notMem (by simp [h1a, h1a2, h1b]),
      Finset.card_insert_of_notMem (by simp [haa2, hab]), Finset.card_pair ha2b]
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 3) (by norm_num)
  have := Finset.card_le_card hsub
  omega

end MinPar

section Module

variable {W : Type*} [CommGroup W] [Finite W]

theorem mem_four {U : Subgroup W} (hU : Nat.card U = 4) (hsq : ∀ x : W, x * x = 1) {w u x : W}
    (hw : w ∈ U) (hu : u ∈ U) (hx : x ∈ U) (hw1 : w ≠ 1) (hu1 : u ≠ 1) (huw : u ≠ w) :
    x = 1 ∨ x = w ∨ x = u ∨ x = w * u := by
  classical
  have : Fintype W := Fintype.ofFinite W
  by_contra hne
  push Not at hne
  obtain ⟨hx1, hxw, hxu, hxwu⟩ := hne
  have hwu1 : w * u ≠ 1 := fun h => huw (by
    have := congrArg (w * ·) h
    simp only [← mul_assoc, hsq w, one_mul, mul_one] at this
    exact this)
  have hwuw : w * u ≠ w := fun h => hu1 (by
    have := congrArg (w⁻¹ * ·) h
    simpa using this)
  have hwuu : w * u ≠ u := fun h => hw1 (by
    have := congrArg (· * u⁻¹) h
    simpa using this)
  let S : Finset W := {1, w, u, w * u, x}
  have hS : S.card = 5 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hw1, Ne.symm hu1, Ne.symm hwu1,
      Ne.symm hx1]), Finset.card_insert_of_notMem (by simp [Ne.symm huw, Ne.symm hwuw,
      Ne.symm hxw]), Finset.card_insert_of_notMem (by simp [Ne.symm hwuu, Ne.symm hxu]),
      Finset.card_pair (Ne.symm hxwu)]
  have hsub : S ⊆ (U : Set W).toFinset := by
    intro y hy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Set.mem_toFinset, SetLike.mem_coe]
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact U.one_mem
    · exact hw
    · exact hu
    · exact U.mul_mem hw hu
    · exact hx
  have hcardU : (U : Set W).toFinset.card = 4 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, ← hU]
    rfl
  have := Finset.card_le_card hsub
  omega

theorem fix_of_orderOf_eq_three {U : Subgroup W} (hU : Nat.card U = 4)
    (hsq : ∀ x : W, x * x = 1) {f : MulAut W} (hf3 : orderOf f = 3) (hst : ∀ u ∈ U, f u ∈ U)
    {w : W} (hw : w ∈ U) (hw1 : w ≠ 1) (hfw : f w = w) : ∀ u ∈ U, f u = u := by
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
  by_cases huw : u = w
  · rw [huw, hfw]
  have hfu1 : f u ≠ 1 := fun h => hu1 (f.injective (by rw [h, map_one]))
  have hfuw : f u ≠ w := fun h => huw (f.injective (by rw [h, hfw]))
  rcases mem_four hU hsq hw hu (hst u hu) hw1 hu1 huw with h | h | h | h
  · exact absurd h hfu1
  · exact absurd h hfuw
  · exact h
  · exfalso
    have h2 : f (w * u) = u := by rw [map_mul, hfw, h, ← mul_assoc, hsq, one_mul]
    have h3 : (f ^ 3) u = w * u := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, h, h2]
    rw [← hf3, pow_orderOf_eq_one, MulAut.one_apply] at h3
    apply hw1
    have := congrArg (· * u⁻¹) h3
    simpa using this.symm

end Module

section BlocksModule

variable {H : Subgroup G} {hV} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

theorem Blocks.eq_one_of_orderOf_eq_three (B : Blocks hV H 𝓗 I)
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) {f : MulAut (IntMod V hV)} (hf : f ∈ L)
    (hf3 : orderOf f = 3) {w : IntMod V hV} (hw : w ∈ commSub ⊤ L) (hfw : f w = w) :
    w = 1 := by
  by_contra hw1
  have hsq : ∀ x : IntMod V hV, x * x = 1 := fun x => by rw [← pow_two]; exact IntMod.sq_eq_one x
  have hfix := fix_of_orderOf_eq_three (B.hb.card_comm L (B.sub hL)) hsq hf3
    (fun u hu => B.hb.stab L (B.sub hL) f hf u hu) hw hw1 hfw
  have hfC : f ∈ L ⊓ centSub (commSub ⊤ L) := ⟨hf, mem_centSub.mpr hfix⟩
  rw [B.hb.inf_centSub (B.sub hL), Subgroup.mem_bot] at hfC
  rw [hfC, orderOf_one] at hf3
  norm_num at hf3

theorem Blocks.exists_fix (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) {t : MulAut (IntMod V hV)} (ht : t ∈ L) (ht2 : orderOf t = 2) :
    ∃ c ∈ commSub ⊤ L, c ≠ 1 ∧ t c = c := by
  have hsq : ∀ x : IntMod V hV, x * x = 1 := fun x => by rw [← pow_two]; exact IntMod.sq_eq_one x
  have hU4 := B.hb.card_comm L (B.sub hL)
  obtain ⟨u, hu1⟩ : ∃ u : commSub (⊤ : Subgroup (IntMod V hV)) L, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (commSub (⊤ : Subgroup (IntMod V hV)) L) := ⟨fun a b => by
      rw [hcon a, hcon b]⟩
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  have hu1' : (u : IntMod V hV) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have htt : ∀ x : IntMod V hV, t (t x) = x := fun x => by
    rw [← MulAut.mul_apply, ← pow_two, ← ht2, pow_orderOf_eq_one, MulAut.one_apply]
  by_cases htu : t u = u
  · exact ⟨u, u.2, hu1', htu⟩
  · refine ⟨u * t u, Subgroup.mul_mem _ u.2 (B.hb.stab L (B.sub hL) t ht u u.2), ?_, ?_⟩
    · intro h
      apply htu
      have := congrArg ((u : IntMod V hV) * ·) h
      simp only [← mul_assoc, hsq, one_mul, mul_one] at this
      exact this
    · rw [map_mul, htt, mul_comm]

theorem Blocks.mem_zpowers_of_fix (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) {t : MulAut (IntMod V hV)} (ht : t ∈ L) (ht2 : orderOf t = 2)
    {c : IntMod V hV} (hc : c ∈ commSub ⊤ L) (hc1 : c ≠ 1) (htc : t c = c)
    {l : MulAut (IntMod V hV)} (hl : l ∈ L) (hlc : l c = c) : l ∈ Subgroup.zpowers t := by
  set S : Subgroup (MulAut (IntMod V hV)) := L ⊓ MulAction.stabilizer (MulAut (IntMod V hV)) c
    with hS
  have htS : t ∈ S := ⟨ht, htc⟩
  have hlS : l ∈ S := ⟨hl, hlc⟩
  have h3 : ¬ 3 ∣ Nat.card S := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 h3
    have hf3 : orderOf (f : MulAut (IntMod V hV)) = 3 := by rw [Subgroup.orderOf_coe, hf]
    exact hc1 (B.eq_one_of_orderOf_eq_three hL f.2.1 hf3 hc f.2.2)
  have h2 : 2 ∣ Nat.card S := by
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 htS)
    rwa [Nat.card_zpowers, ht2] at this
  have h6 : Nat.card S ∣ 6 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : S ≤ L)
    rwa [B.card_eq hL] at this
  have hS2 : Nat.card S = 2 := by
    have hpos : 0 < Nat.card S := Nat.card_pos
    have : Nat.card S ≤ 6 := Nat.le_of_dvd (by norm_num) h6
    interval_cases h : Nat.card S <;> simp_all
  have heq : Subgroup.zpowers t = S :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 htS) (by rw [hS2, Nat.card_zpowers, ht2])
  rw [heq]
  exact hlS

end BlocksModule

end E2

end CFSG.Quasithin
