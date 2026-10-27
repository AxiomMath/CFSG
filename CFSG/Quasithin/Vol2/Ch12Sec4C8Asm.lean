module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Stmt
public import CFSG.Quasithin.Background.E6TwentyTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S1248



namespace S1248

theorem three_dvd_card_psl2 {K : Type} [Group K] {p : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 2 p 1) : 3 ∣ Nat.card K := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have hF' : Nat.card F = p := by rw [hF, pow_one]
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2) (by norm_num), hF']
  have hprod : ∏ j ∈ Finset.Icc 2 2, (p ^ j - 1) = (p + 1) * (p - 1) := by
    rw [Finset.Icc_self, Finset.prod_singleton]
    have := Nat.sq_sub_sq p 1
    simpa using this
  have he : p ^ (2 * (2 - 1) / 2) = p := by norm_num
  rw [hprod, he]
  have hN : 3 ∣ p * ((p + 1) * (p - 1)) := by
    rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
    · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _
    · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega)) _) _
  have hd : Nat.gcd 2 (p - 1) ∣ p * ((p + 1) * (p - 1)) :=
    (Nat.gcd_dvd_right 2 (p - 1)).trans (Dvd.dvd.mul_left (Dvd.intro_left (p + 1) rfl) _)
  have hcop : Nat.Coprime 3 (Nat.gcd 2 (p - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 (p - 1)) (by norm_num)
  obtain ⟨k, hk⟩ := hd
  rw [hk, Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_left _ (by norm_num))]
  rw [hk] at hN
  exact hcop.dvd_of_dvd_mul_left hN

end S1248

theorem noComp1248_of (hX : HypX1248) (hT : Comp1248Type) (hL : Comp1248Lift) : NoComp1248 := by
  intro G _ _ T L V U hS K hK
  obtain ⟨hnotY, -, ⟨p, hp, hpsl⟩, -, hCK⟩ := hT G T L V U hS K hK
  rcases hX G T L V U hS with ⟨X, hXLU, hX3, hXC, l, hl, hlU, hl2⟩ | hY
  · obtain ⟨hK0, huniq⟩ := hL G T L V U hS X hXLU hX3 hXC l hl hlU hl2 K hK ⟨p, hp, hpsl⟩
    have hlU₀ : CFSG.conjugate (U ⊓ conjSubgroup U l) l = U ⊓ conjSubgroup U l := by
      ext x
      rw [QuasithinUnique.BenderBranch.mem_conjugate_iff, Subgroup.mem_inf, Subgroup.mem_inf,
        mem_conjSubgroup_iff, mem_conjSubgroup_iff]
      have h2 := Subgroup.mem_normalizer_iff.1 hl2 x
      have e : l * (l * x * l⁻¹) * l⁻¹ = l ^ 2 * x * (l ^ 2)⁻¹ := by
        rw [sq, mul_inv_rev]
        simp only [mul_assoc]
      rw [e, ← h2]
      exact and_comm
    have hK' := E6.isComponentIn_conjugate' hK0 l
    rw [hlU₀] at hK'
    have h3 : 3 ∣ Nat.card ↥(CFSG.conjugate K l) := by
      rw [CFSG.conjugate,
        Subgroup.card_map_of_injective (f := (MulAut.conj l⁻¹).toMonoidHom)
          (MulAut.conj l⁻¹).injective]
      exact S1248.three_dvd_card_psl2 hpsl
    have hKl : CFSG.conjugate K l = K := huniq _ hK' h3
    have hKUl : K ≤ Subgroup.centralizer ((conjSubgroup U l : Subgroup G) : Set G) := by
      have := (E6.isComponentIn_conjugate' hK l).1
      rw [hKl] at this
      exact this
    have hUl_le : conjSubgroup U l ≤ U := by
      have hle : conjSubgroup U l ≤ V ⊓ Subgroup.centralizer (K : Set G) := by
        refine le_inf ?_ (Subgroup.le_centralizer_iff.mp hKUl)
        intro x hx
        rw [mem_conjSubgroup_iff] at hx
        have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hl.1)
          (l * x * l⁻¹)).1 (hS.le hx)
        have e : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
        rwa [e] at h1
      rwa [hCK] at hle
    have hcard : Nat.card ↥(conjSubgroup U l) = Nat.card ↥U := by
      rw [conjSubgroup,
        Subgroup.card_map_of_injective (f := (MulAut.conj l⁻¹).toMonoidHom)
          (MulAut.conj l⁻¹).injective]
    have heq : conjSubgroup U l = U := Subgroup.eq_of_le_of_card_ge hUl_le hcard.ge
    exact hlU (QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.1 heq)
  · exact hnotY hY



namespace S1248

variable {G : Type} [Group G]

theorem commute_of_inverts {x y z : G} (hx : z * x * z⁻¹ = x⁻¹) (hy : z * y * z⁻¹ = y⁻¹)
    (hxy : z * (x * y * x⁻¹) * z⁻¹ = (x * y * x⁻¹)⁻¹) (hodd : Odd (orderOf x)) :
    x * y = y * x := by
  have h1 : z * (x * y * x⁻¹) * z⁻¹ = x⁻¹ * y⁻¹ * x := by
    have e : z * (x * y * x⁻¹) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) * (z * x * z⁻¹)⁻¹ := by
      group
    rw [e, hx, hy, inv_inv]
  rw [h1] at hxy
  have h2 : x ^ 2 * y⁻¹ = y⁻¹ * x ^ 2 := by
    have e : x⁻¹ * y⁻¹ * x = x * y⁻¹ * x⁻¹ := by rw [hxy]; group
    rw [sq]
    calc x * x * y⁻¹ = x * (x * y⁻¹ * x⁻¹) * x := by group
      _ = x * (x⁻¹ * y⁻¹ * x) * x := by rw [e]
      _ = y⁻¹ * (x * x) := by group
  have h3 : Commute (x ^ 2) y := (Commute.inv_right_iff).1 h2
  obtain ⟨m, hm⟩ := hodd
  have hx' : (x ^ 2) ^ (m + 1) = x := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h4 := h3.pow_left (m + 1)
  rw [hx'] at h4
  exact h4.eq

theorem commute_of_inverts_all {A : Subgroup G} {z : G} (h : ∀ x ∈ A, z * x * z⁻¹ = x⁻¹)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have hab := h _ (A.mul_mem ha hb)
  have e : z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
  rw [e, h a ha, h b hb, mul_inv_rev] at hab
  have := congrArg (fun w => w⁻¹) hab
  simpa using this.symm

theorem exists_odd_pow_eq_one_of_closure {S : Set G} (hS : ∀ s ∈ S, Odd (orderOf s))
    (hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a) :
    ∀ n ∈ Subgroup.closure S, ∃ m : ℕ, Odd m ∧ n ^ m = 1 := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact ⟨orderOf x, hS x hx, pow_orderOf_eq_one x⟩
  | one => exact ⟨1, odd_one, one_pow 1⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨m₁, hm₁, h₁⟩ := ihx
    obtain ⟨m₂, hm₂, h₂⟩ := ihy
    refine ⟨m₁ * m₂, hm₁.mul hm₂, ?_⟩
    rw [(Commute.mul_pow (hcomm x hx y hy) (m₁ * m₂)), pow_mul, h₁, one_pow, mul_comm, pow_mul,
      h₂, one_pow, one_mul]
  | inv x hx ihx =>
    obtain ⟨m, hm, h⟩ := ihx
    exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩

variable [Finite G]

theorem odd_card_of_forall_odd_pow {N : Subgroup G} (h : ∀ n ∈ N, ∃ m : ℕ, Odd m ∧ n ^ m = 1) :
    Odd (Nat.card N) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
  obtain ⟨m, hm, hnm⟩ := h n n.2
  have h1 : (n : G) ^ m = 1 := hnm
  have h2' : n ^ m = 1 := Subtype.ext (by simpa using h1)
  have := orderOf_dvd_of_pow_eq_one h2'
  rw [hn] at this
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 this)

theorem le_oddCoreIn_of_centralizes {H O : Subgroup G} (hOH : O ≤ H)
    (hodd : ∀ x ∈ O, Odd (orderOf x))
    (hQ : O ≤ Subgroup.centralizer (pCoreOf 2 H : Set G))
    (hOd : O ≤ Subgroup.centralizer (QuasithinUnique.oddCoreIn H : Set G))
    (hE : ∀ K, QuasithinUnique.IsComponentIn K H → O ≤ Subgroup.centralizer (K : Set G)) :
    O ≤ QuasithinUnique.oddCoreIn H := by
  set N := conjClosure O H with hNdef
  have hNH : N ≤ H := conjClosure_le fun h hh o ho => H.mul_mem (H.mul_mem hh (hOH ho))
    (H.inv_mem hh)
  have hnorm : H ≤ Subgroup.normalizer (N : Set G) := le_normalizer_conjClosure O H
  have hcentN : ∀ X : Subgroup G,
      (∀ h ∈ H, O ≤ Subgroup.centralizer ((CFSG.conjugate X h : Subgroup G) : Set G)) →
        N ≤ Subgroup.centralizer (X : Set G) := by
    intro X hX
    refine conjClosure_le fun h hh o ho => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : h⁻¹ * x * h ∈ CFSG.conjugate X h := by
      rw [QuasithinUnique.BenderBranch.mem_conjugate_iff]
      simpa [mul_assoc] using hx
    have hc := Subgroup.mem_centralizer_iff.1 (hX h hh ho) _ hx'
    calc x * (h * o * h⁻¹) = h * ((h⁻¹ * x * h) * o) * h⁻¹ := by group
      _ = h * (o * (h⁻¹ * x * h)) * h⁻¹ := by rw [hc]
      _ = h * o * h⁻¹ * x := by group
  have hnormal : ∀ X : Subgroup G, H ≤ Subgroup.normalizer (X : Set G) →
      O ≤ Subgroup.centralizer (X : Set G) → N ≤ Subgroup.centralizer (X : Set G) := by
    intro X hX hOX
    refine hcentN X fun h hh => ?_
    rw [QuasithinUnique.BenderBranch.conjugate_eq_iff_mem_normalizer.2 (hX hh)]
    exact hOX
  have hNQ := hnormal _ (LieType.BorelTits.le_normalizer_pCoreOf 2 H) hQ
  have hNO := hnormal _ (QuasithinUnique.le_normalizer_oddCoreIn H) hOd
  have hNE : ∀ K, QuasithinUnique.IsComponentIn K H → N ≤ Subgroup.centralizer (K : Set G) :=
    fun K hK => hcentN K fun h hh =>
      hE _ (QuasithinUnique.Unc25G2.isComponentIn_conjugate hK hh)
  have hfit : CFSG.fittingSubgroup ↥H ≤ CFSG.pCore 2 ↥H ⊔ CFSG.oddCore ↥H := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 2
    · rw [hp]
      exact le_sup_left
    · refine le_trans ?_ le_sup_right
      have hq : Nat.Prime p.1.1 := Nat.prime_of_mem_primeFactors p.1.2
      have hqodd : Odd p.1.1 := hq.odd_of_ne_two hp
      refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p.1.1) (G := ↥H)).exists_card_eq
      rw [hn]
      exact hqodd.pow
  have hFN : CFSG.generalizedFitting ↥H ≤
      Subgroup.centralizer ((N.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [CFSG.generalizedFitting]
    refine sup_le (hfit.trans (sup_le ?_ ?_)) ?_
    · intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hw' : (w : G) ∈ pCoreOf 2 H := by
        rw [pCoreOf]
        exact ⟨w, hw, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hNQ hn) _ hw').symm
    · intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hw' : (w : G) ∈ QuasithinUnique.oddCoreIn H := ⟨w, hw, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hNO hn) _ hw').symm
    · refine sSup_le fun K hK => ?_
      have hKc : QuasithinUnique.IsComponentIn (K.map H.subtype) H := by
        refine ⟨Subgroup.map_subtype_le K, ?_⟩
        have : (K.map H.subtype).subgroupOf H = K :=
          Subgroup.comap_map_eq_self_of_injective Subtype.val_injective K
        rw [this]
        exact hK
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hNE _ hKc hn) _ ⟨w, hw, rfl⟩).symm
  have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    have ha' : (⟨a, hNH ha⟩ : ↥H) ∈
        Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) :=
      Subgroup.le_centralizer_iff.1 hFN (Subgroup.mem_subgroupOf.2 ha)
    have hb' : (⟨b, hNH hb⟩ : ↥H) ∈ CFSG.generalizedFitting ↥H :=
      CFSG.centralizer_generalizedFitting_le ↥H
        (Subgroup.le_centralizer_iff.1 hFN (Subgroup.mem_subgroupOf.2 hb))
    have := Subgroup.mem_centralizer_iff.1 ha' _ hb'
    exact (congrArg Subtype.val this).symm
  have hoddN : Odd (Nat.card N) := by
    refine odd_card_of_forall_odd_pow ?_
    have hS : ∀ s ∈ {x | ∃ h ∈ H, ∃ z ∈ O, h * z * h⁻¹ = x}, Odd (orderOf s) := by
      rintro s ⟨h, -, o, ho, rfl⟩
      have e : h * o * h⁻¹ = (MulAut.conj h).toMonoidHom o := by simp [MulAut.conj_apply]
      rw [e, orderOf_injective _ (MulAut.conj h).injective]
      exact hodd o ho
    exact exists_odd_pow_eq_one_of_closure hS hNcomm
  exact (le_conjClosure O H).trans
    (QuasithinUnique.DoubleA3.le_oddCoreIn_of_odd hNH hnorm hoddN)

end S1248



namespace S1248

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_inf_eq_two {V U U' : Subgroup G} (hU : U ≤ V) (hU' : U' ≤ V)
    (h1 : U.relIndex V = 2) (h2 : U'.relIndex V = 2) (hne : U ≠ U') :
    (U ⊓ U').relIndex U = 2 := by
  rw [Subgroup.inf_relIndex_left]
  set A := U.subgroupOf V
  set B := U'.subgroupOf V
  have hA : A.index = 2 := h1
  have hB : B.index = 2 := h2
  have hBn : B.Normal := Subgroup.normal_of_index_eq_two hB
  have hAB : A ⊔ B = ⊤ := by
    by_contra hne'
    have hmul := Subgroup.relIndex_mul_index (le_sup_left : A ≤ A ⊔ B)
    rw [hA] at hmul
    have hidx1 : (A ⊔ B).index ≠ 1 := fun h => hne' (Subgroup.index_eq_one.1 h)
    have hdvd : (A ⊔ B).index ∣ 2 := Dvd.intro_left _ hmul
    have h2' : (A ⊔ B).index = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd h hidx1
      · exact h
    rw [h2'] at hmul
    have h1' : A.relIndex (A ⊔ B) = 1 := by omega
    have hBA : B ≤ A := le_sup_right.trans (Subgroup.relIndex_eq_one.1 h1')
    have hmul' := Subgroup.relIndex_mul_index hBA
    rw [hA, hB] at hmul'
    have h1'' : B.relIndex A = 1 := by omega
    have hAB' : A = B := le_antisymm (Subgroup.relIndex_eq_one.1 h1'') hBA
    apply hne
    have := (Subgroup.subgroupOf_inj).1 hAB'
    rwa [inf_eq_left.2 hU, inf_eq_left.2 hU'] at this
  have := Subgroup.relIndex_sup_right A B
  rw [hAB, Subgroup.relIndex_top_right, hB] at this
  rw [← Subgroup.relIndex_subgroupOf hU]
  exact this.symm

end S1248

theorem oddCore1248_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (hInv : OddInv1248) (hE : OddCentE1248) (hQ : OddCentQ1248) (hF : OddFinal1248) :
    OddCore1248 := by
  intro G _ _ T L V U hS
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hS.cx hS.quot
  have hzVL : z ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hf.zV]
    exact Subgroup.mem_zpowers z
  have hz1 : z ≠ 1 := by
    intro h
    have := hf.order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hoddO : ∀ W : Subgroup G,
      ∀ x ∈ QuasithinUnique.oddCoreIn (Subgroup.centralizer (W : Set G)), Odd (orderOf x) :=
    fun W x hx => Odd.of_dvd_nat (QuasithinUnique.odd_card_oddCoreIn _)
      (Subgroup.orderOf_dvd_natCard _ hx)
  have hsub : ∀ U' : Subgroup G, Setting G T L V U' → ∀ U₀ : Subgroup G, U₀ ≤ U' →
      U₀.relIndex U' = 2 → QuasithinUnique.oddCoreIn (Subgroup.centralizer (U' : Set G)) ≤
        QuasithinUnique.oddCoreIn (Subgroup.centralizer (U₀ : Set G)) := by
    intro U' hS' U₀ hU₀ hidx
    refine S1248.le_oddCoreIn_of_centralizes
      ((QuasithinUnique.oddCoreIn_le _).trans (Subgroup.centralizer_le hU₀)) (hoddO U')
      (hQ G T L V U' hS' U₀ hU₀ hidx) ?_ (hE G T L V U' hS' U₀ hU₀ hidx)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxH : x ∈ Subgroup.centralizer (U₀ : Set G) :=
      Subgroup.centralizer_le hU₀ (QuasithinUnique.oddCoreIn_le _ hx)
    have hxy : x * y * x⁻¹ ∈ QuasithinUnique.oddCoreIn (Subgroup.centralizer (U₀ : Set G)) :=
      (Subgroup.mem_normalizer_iff.1 (QuasithinUnique.le_normalizer_oddCoreIn _ hxH) y).1 hy
    have hinvU' := hInv G T L V U' hS' z hzVL hz1 U' (Or.inl rfl)
    have hinvU₀ := hInv G T L V U' hS' z hzVL hz1 U₀ (Or.inr ⟨hU₀, hidx⟩)
    exact (S1248.commute_of_inverts (hinvU' x hx) (hinvU₀ y hy) (hinvU₀ _ hxy)
      (hoddO U' x hx)).symm
  have hMV : ∀ m ∈ Subgroup.normalizer (L : Set G), m ∈ Subgroup.normalizer (V : Set G) :=
    fun m hm => by rw [← hf.MN]; exact hm
  have hmapV : ∀ m ∈ Subgroup.normalizer (L : Set G), V.map (MulAut.conj m).toMonoidHom = V := by
    intro m hm
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have h := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hMV m hm)) x
    rw [inv_inv] at h
    exact h.symm
  have hconjS : ∀ m ∈ Subgroup.normalizer (L : Set G),
      Setting G T L V (U.map (MulAut.conj m).toMonoidHom) := by
    intro m hm
    refine ⟨hS.cx, hS.quot, ?_, ?_, ?_⟩
    · rw [← hmapV m hm]
      exact Subgroup.map_mono hS.le
    · rw [← hmapV m hm, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj m).injective]
      exact hS.hyper
    · intro hle
      apply hS.escape
      intro c hc
      have hc' : m * c * m⁻¹ ∈ Subgroup.centralizer
          ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨u, hu, rfl⟩
        have := Subgroup.mem_centralizer_iff.1 hc u hu
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc m * u * m⁻¹ * (m * c * m⁻¹) = m * (u * c) * m⁻¹ := by group
          _ = m * (c * u) * m⁻¹ := by rw [this]
          _ = m * c * m⁻¹ * (m * u * m⁻¹) := by group
      have h1 := hle hc'
      have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMV m hm)) h1)
        (hMV m hm)
      simpa [mul_assoc] using h2
  set O := QuasithinUnique.oddCoreIn (Subgroup.centralizer (U : Set G)) with hOdef
  have hOconj : ∀ m : G, O.map (MulAut.conj m).toMonoidHom ≤ QuasithinUnique.oddCoreIn
      (Subgroup.centralizer ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) := by
    intro m
    have hCm : Subgroup.centralizer ((U.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) =
        (Subgroup.centralizer (U : Set G)).map (MulAut.conj m).toMonoidHom := by
      ext c
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_centralizer_iff,
        Subgroup.mem_centralizer_iff]
      constructor
      · intro h u hu
        have := h (m * u * m⁻¹) ⟨u, hu, by simp [MulAut.conj_apply]⟩
        calc u * (m⁻¹ * c * m) = m⁻¹ * ((m * u * m⁻¹) * c) * m := by group
          _ = m⁻¹ * (c * (m * u * m⁻¹)) * m := by rw [this]
          _ = m⁻¹ * c * m * u := by group
      · rintro h _ ⟨u, hu, rfl⟩
        have := h u hu
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc m * u * m⁻¹ * c = m * (u * (m⁻¹ * c * m)) * m⁻¹ := by group
          _ = m * ((m⁻¹ * c * m) * u) * m⁻¹ := by rw [this]
          _ = c * (m * u * m⁻¹) := by group
    rw [hCm]
    refine QuasithinUnique.DoubleA3.le_oddCoreIn_of_odd (Subgroup.map_mono
      (QuasithinUnique.oddCoreIn_le _)) ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨c * y * c⁻¹, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        exact (Subgroup.mem_normalizer_iff.1 (QuasithinUnique.le_normalizer_oddCoreIn _ hc) y).1
          hy
      · rintro ⟨y, hy, hyx⟩
        refine ⟨c⁻¹ * y * c, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.1
            (QuasithinUnique.le_normalizer_oddCoreIn _ (Subgroup.inv_mem _ hc)) y).1 hy
          simpa using this
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx ⊢
          have hx : x = (m * c * m⁻¹)⁻¹ * (m * y * m⁻¹) * (m * c * m⁻¹) := by
            rw [hyx]
            group
          rw [hx]
          group
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj m).toMonoidHom)
        (MulAut.conj m).injective]
      exact QuasithinUnique.odd_card_oddCoreIn _
  have hinvU := hInv G T L V U hS z hzVL hz1 U (Or.inl rfl)
  have hcommOm : ∀ m ∈ Subgroup.normalizer (L : Set G), ∀ a ∈ O,
      ∀ b ∈ O.map (MulAut.conj m).toMonoidHom, a * b = b * a := by
    intro m hm a ha b hb
    by_cases hmU : U.map (MulAut.conj m).toMonoidHom = U
    · have hb' := hOconj m hb
      rw [hmU] at hb'
      exact S1248.commute_of_inverts_all hinvU ha hb'
    · set U' := U.map (MulAut.conj m).toMonoidHom
      have hS' := hconjS m hm
      have h1 : (U ⊓ U').relIndex U = 2 :=
        S1248.relIndex_inf_eq_two hS.le hS'.le hS.hyper hS'.hyper (Ne.symm hmU)
      have h2 : (U' ⊓ U).relIndex U' = 2 :=
        S1248.relIndex_inf_eq_two hS'.le hS.le hS'.hyper hS.hyper hmU
      rw [inf_comm] at h2
      have ha' := hsub U hS (U ⊓ U') inf_le_left h1 ha
      have hb' := hsub U' hS' (U ⊓ U') inf_le_right h2 (hOconj m hb)
      have hinv0 := hInv G T L V U hS z hzVL hz1 (U ⊓ U') (Or.inr ⟨inf_le_left, h1⟩)
      exact S1248.commute_of_inverts_all hinv0 ha' hb'
  by_contra hne
  set P := conjClosure O (Subgroup.normalizer (L : Set G)) with hPdef
  have hgen : ∀ a ∈ {x | ∃ h ∈ Subgroup.normalizer (L : Set G), ∃ o ∈ O, h * o * h⁻¹ = x},
      ∀ b ∈ {x | ∃ h ∈ Subgroup.normalizer (L : Set G), ∃ o ∈ O, h * o * h⁻¹ = x},
        a * b = b * a := by
    rintro _ ⟨m₁, hm₁, o₁, ho₁, rfl⟩ _ ⟨m₂, hm₂, o₂, ho₂, rfl⟩
    have hm : m₁⁻¹ * m₂ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hm₁) hm₂
    have hb : (m₁⁻¹ * m₂) * o₂ * (m₁⁻¹ * m₂)⁻¹ ∈ O.map (MulAut.conj (m₁⁻¹ * m₂)).toMonoidHom :=
      ⟨o₂, ho₂, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hc := hcommOm _ hm o₁ ho₁ _ hb
    calc m₁ * o₁ * m₁⁻¹ * (m₂ * o₂ * m₂⁻¹)
        = m₁ * (o₁ * ((m₁⁻¹ * m₂) * o₂ * (m₁⁻¹ * m₂)⁻¹)) * m₁⁻¹ := by group
      _ = m₁ * (((m₁⁻¹ * m₂) * o₂ * (m₁⁻¹ * m₂)⁻¹) * o₁) * m₁⁻¹ := by rw [hc]
      _ = m₂ * o₂ * m₂⁻¹ * (m₁ * o₁ * m₁⁻¹) := by group
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    have hS1 : Subgroup.closure {x | ∃ h ∈ Subgroup.normalizer (L : Set G), ∃ o ∈ O,
        h * o * h⁻¹ = x} ≤ Subgroup.centralizer {x | ∃ h ∈ Subgroup.normalizer (L : Set G),
          ∃ o ∈ O, h * o * h⁻¹ = x} := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro b hb
      exact hgen b hb a ha
    intro a ha b hb
    have hb' : b ∈ Subgroup.centralizer (P : Set G) := by
      rw [hPdef, conjClosure, Subgroup.centralizer_closure]
      exact hS1 hb
    exact Subgroup.mem_centralizer_iff.1 hb' a ha
  have hPodd : Odd (Nat.card P) := by
    refine S1248.odd_card_of_forall_odd_pow ?_
    have hS2 : ∀ s ∈ {x | ∃ h ∈ Subgroup.normalizer (L : Set G), ∃ o ∈ O, h * o * h⁻¹ = x},
        Odd (orderOf s) := by
      rintro s ⟨h, -, o, ho, rfl⟩
      have e : h * o * h⁻¹ = (MulAut.conj h).toMonoidHom o := by simp [MulAut.conj_apply]
      rw [e, orderOf_injective _ (MulAut.conj h).injective]
      exact hoddO U o ho
    exact S1248.exists_odd_pow_eq_one_of_closure hS2 hPcomm
  have hPne : P ≠ ⊥ := fun h => hne (le_bot_iff.1 (h ▸ le_conjClosure O _))
  have hPab : IsMulCommutative ↥P :=
    ⟨⟨fun a b => Subtype.ext (hPcomm a a.2 b b.2)⟩⟩
  have hVP := hF G T L V U hS P hPne hPodd hPab (le_normalizer_conjClosure O _)
  apply hne
  rw [eq_bot_iff]
  intro x hx
  have hzx := Subgroup.mem_centralizer_iff.1 (hVP hzVL.1) x (le_conjClosure O _ hx)
  have hinv := hinvU x hx
  have hxx : x = x⁻¹ := by
    rw [← hinv, ← hzx]
    group
  have hx2 : x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hxx]
    exact mul_inv_cancel x
  have hord := orderOf_dvd_of_pow_eq_one hx2
  have hodd := hoddO U x hx
  rw [Subgroup.mem_bot]
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1


end CFSG.Quasithin.H13
