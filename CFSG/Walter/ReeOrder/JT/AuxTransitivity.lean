module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
import CFSG.Walter.Transitivity.Family
import CFSG.Walter.Transitivity.OddCore
import CFSG.Walter.Transitivity.Coprime
import CFSG.Walter.Transitivity.Step

public section

namespace CFSG.Walter.JT

open CFSG CFSG.Walter.Transitivity

theorem card_le_of_isCyclic_of_pow_eq_one {E : Type*} [Group E] [IsCyclic E] {p : ℕ}
    (hp : 0 < p) (hexp : ∀ x : E, x ^ p = 1) : Nat.card E ≤ p := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hp (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_smul_eq_conj {V Q : Subgroup G} [Subgroup.Normalizes V Q]
    {v : V} {x : Q} (h : v • x = x) :
    (x : G) ∈ Subgroup.centralizer ({(v : G)} : Set G) := by
  have h' : (v : G) * x * (v : G)⁻¹ = x := by
    simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact Subgroup.mem_centralizer_singleton_iff.mpr h'.symm

theorem exists_ne_one_centralizer_not_le_of_prime {p : ℕ} [hp : Fact p.Prime]
    {V Q₁ Q₂ D : Subgroup G}
    (hVcomm : IsMulCommutative V) (hVexp : ∀ x ∈ V, x ^ p = 1) (hVcard : p ^ 3 ≤ Nat.card V)
    (hQ₁ : Nat.Coprime p (Nat.card Q₁)) (hQ₂ : Nat.Coprime p (Nat.card Q₂))
    (hVQ₁ : V ≤ Subgroup.normalizer (Q₁ : Set G))
    (hVQ₂ : V ≤ Subgroup.normalizer (Q₂ : Set G)) (hQ₁D : ¬ Q₁ ≤ D) (hQ₂D : ¬ Q₂ ≤ D) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ Q₁ ⊓ Subgroup.centralizer ({v} : Set G) ≤ D ∧
      ¬ Q₂ ⊓ Subgroup.centralizer ({v} : Set G) ≤ D := by
  classical
  let : CommGroup V := IsMulCommutative.instCommGroup
  have hp2 := hp.out.two_le
  have hexp : ∀ x : V, x ^ p = 1 := fun x => Subtype.ext (hVexp x x.2)
  have hVp : IsPGroup p V := fun x => ⟨1, by simpa using hexp x⟩
  have : Fact (IsPGroup p V) := ⟨hVp⟩
  have : Subgroup.Normalizes V Q₁ := ⟨hVQ₁⟩
  have : Subgroup.Normalizes V Q₂ := ⟨hVQ₂⟩
  have hp3 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp2 (by norm_num)
  have hVnc : ¬ IsCyclic V := fun _ => by
    have := card_le_of_isCyclic_of_pow_eq_one hp.out.pos hexp
    omega
  have hsup₁ := iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
    (G := Q₁) (A := V) p hQ₁ hVnc
  obtain ⟨B, hBcyc, hBfix⟩ : ∃ B : Subgroup V, IsCyclic (V ⧸ B) ∧
      ¬ fixedPointSubgroup B Q₁ ≤ D.subgroupOf Q₁ := by
    by_contra! h
    apply hQ₁D
    intro x hx
    have htop : (⊤ : Subgroup Q₁) ≤ D.subgroupOf Q₁ := hsup₁ ▸ iSup₂_le h
    exact htop (Subgroup.mem_top ⟨x, hx⟩)
  have hBnc : ¬ IsCyclic B := fun _ => by
    have h₁ : Nat.card (V ⧸ B) ≤ p := card_le_of_isCyclic_of_pow_eq_one hp.out.pos fun x => by
      induction x using QuotientGroup.induction_on with
      | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
    have h₂ : Nat.card B ≤ p :=
      card_le_of_isCyclic_of_pow_eq_one hp.out.pos fun x => Subtype.ext (hexp x)
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup B
    have := Nat.mul_le_mul h₁ h₂
    have hp2' : p * p < p ^ 3 := by
      calc p * p = p ^ 2 := (sq p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp2 (by norm_num)
    omega
  have : Fact (IsPGroup p B) := ⟨hVp.to_subgroup B⟩
  have hsup₂ := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := Q₂) (A := B) p hQ₂ hBnc
  obtain ⟨b, hb1, hbfix⟩ : ∃ b : B, b ≠ 1 ∧
      ¬ fixedPointSubgroup (Subgroup.zpowers b) Q₂ ≤ D.subgroupOf Q₂ := by
    by_contra! h
    apply hQ₂D
    intro x hx
    have htop : (⊤ : Subgroup Q₂) ≤ D.subgroupOf Q₂ := hsup₂ ▸ iSup₂_le h
    exact htop (Subgroup.mem_top ⟨x, hx⟩)
  refine ⟨((b : V) : G), (b : V).2, fun h => hb1 (Subtype.ext (Subtype.ext h)), ?_, ?_⟩
  · intro hle
    apply hBfix
    intro x hx
    have hbx : (b : V) • x = x := (FixedPoints.mem_subgroup B Q₁ x).mp hx b
    exact hle ⟨x.2, mem_centralizer_of_smul_eq_conj hbx⟩
  · intro hle
    apply hbfix
    intro x hx
    have hbx : (b : V) • x = x :=
      (FixedPoints.mem_subgroup (Subgroup.zpowers b) Q₂ x).mp hx ⟨b, Subgroup.mem_zpowers b⟩
    exact hle ⟨x.2, mem_centralizer_of_smul_eq_conj hbx⟩

theorem exists_conjBy_of_le_normalizer_of_prime {p : ℕ} [hp : Fact p.Prime]
    {X Q₁ Q₂ V : Subgroup G} {q : Nat.Primes}
    (T : Sylow p G) (hTX : (T : Subgroup G) ≤ X)
    (hVZ : ∀ v ∈ V, ∀ y ∈ (T : Subgroup G), y * v = v * y)
    (hVcomm : IsMulCommutative V) (hVexp : ∀ x ∈ V, x ^ p = 1) (hVcard : p ^ 3 ≤ Nat.card V)
    (hVT : V ≤ T)
    (hsolv : ∀ v ∈ V, v ≠ 1 → Group.IsSolvable (Subgroup.centralizer ({v} : Set G)))
    (hq : q.val ≠ p)
    (hinner : ∀ R₁ ∈ section7HStarFamily X T ({q} : Set Nat.Primes),
      ∀ R₂ ∈ section7HStarFamily X T ({q} : Set Nat.Primes),
      Nat.card (Q₁ ⊓ Q₂ : Subgroup G) < Nat.card (R₁ ⊓ R₂ : Subgroup G) →
        ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
          R₂ = R₁.conjBy (k : G))
    (hQ₁ : Q₁ ∈ section7HStarFamily X T ({q} : Set Nat.Primes))
    (hQ₂ : Q₂ ∈ section7HStarFamily X T ({q} : Set Nat.Primes))
    (h₁₂ : ¬ Q₁ ≤ Q₂) (h₂₁ : ¬ Q₂ ≤ Q₁)
    (hXD : X ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G)) :
    ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
      Q₂ = Q₁.conjBy (k : G) := by
  have : Fact q.val.Prime := ⟨q.2⟩
  have hcop : ∀ {Q : Subgroup G}, IsPiSubgroup ({q} : Set Nat.Primes) Q →
      Nat.Coprime p (Nat.card Q) := by
    intro Q hQ
    obtain ⟨n, hn⟩ := (isPGroup_of_isPiSubgroup_singleton hQ).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp.out q.2).mpr (Ne.symm hq))
  have hDle : ∀ {Q : Subgroup G}, Q ∈ section7HStarFamily X T ({q} : Set Nat.Primes) →
      Q₁ ⊓ Q₂ ≤ Q := by
    intro Q hQ
    have hmem : Q ⊔ (Q₁ ⊓ Q₂) ∈ section7HFamily X T ({q} : Set Nat.Primes) := by
      refine ⟨sup_le hQ.1.1 (inf_le_left.trans hQ₁.1.1), ?_,
        le_normalizer_sup hQ.1.2.2 (le_normalizer_inf hQ₁.1.2.2 hQ₂.1.2.2)⟩
      exact isPiSubgroup_singleton_of_isPGroup
        ((isPGroup_of_isPiSubgroup_singleton hQ.1.2.1).to_sup_of_normal_right'
          (isPGroup_of_isPiSubgroup_singleton (IsPiSubgroup.of_le inf_le_left hQ₁.1.2.1))
          (hQ.1.1.trans hXD))
    exact le_sup_right.trans (hQ.2 _ le_sup_left hmem).le
  obtain ⟨v, hvV, hv1, hv₁, hv₂⟩ := exists_ne_one_centralizer_not_le_of_prime
    (D := Q₁ ⊓ Q₂) hVcomm hVexp hVcard (hcop hQ₁.1.2.1) (hcop hQ₂.1.2.1)
    (hVT.trans hQ₁.1.2.2) (hVT.trans hQ₂.1.2.2)
    (fun h => h₁₂ (h.trans inf_le_right)) (fun h => h₂₁ (h.trans inf_le_left))
  let C : Subgroup G := Subgroup.centralizer ({v} : Set G)
  let Y : Subgroup G := X ⊓ C
  have : Group.IsSolvable C := hsolv v hvV hv1
  have : Group.IsSolvable Y :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (inf_le_right : Y ≤ C))
  have hTC : (T : Subgroup G) ≤ C := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hVZ v hvV y hy)
  have hTY : (T : Subgroup G) ≤ Y := le_inf hTX hTC
  have hTnC : (T : Subgroup G) ≤ Subgroup.normalizer (C : Set G) :=
    hTC.trans Subgroup.le_normalizer
  let K : Subgroup G := (pPrimeCore p Y).map Y.subtype
  have hKY : K ≤ Y := Subgroup.map_subtype_le _
  have hLK : ∀ {Q : Subgroup G}, Q ∈ section7HStarFamily X T ({q} : Set Nat.Primes) →
      Q ⊓ C ≤ K := fun hQ =>
    le_map_pPrimeCore_of_sylow_le_normalizer T hTY (inf_le_inf_right C hQ.1.1)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) (hcop hQ.1.2.1))
      (le_normalizer_inf hQ.1.2.2 hTnC)
  have hcopK : Nat.Coprime (Nat.card (T : Subgroup G)) (Nat.card K) := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (coprime_card_map_pPrimeCore (p := p) Y)
  obtain ⟨S, hSK, hSπ, hTS, hL₁S, c, hc, hL₂S⟩ := exists_conjBy_of_coprime_action
    (hTY.trans (le_normalizer_map_pPrimeCore Y))
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKY)) hcopK
    (hLK hQ₁) (hLK hQ₂) (IsPiSubgroup.of_le inf_le_left hQ₁.1.2.1)
    (IsPiSubgroup.of_le inf_le_left hQ₂.1.2.1) (le_normalizer_inf hQ₁.1.2.2 hTnC)
    (le_normalizer_inf hQ₂.1.2.2 hTnC)
  obtain ⟨Q₃, hQ₃, hSQ₃⟩ := exists_mem_section7HStarFamily_of_mem_family
    (⟨hSK.trans (hKY.trans inf_le_left), hSπ, hTS⟩ :
      S ∈ section7HFamily X T ({q} : Set Nat.Primes))
  have hcX : c ∈ X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) :=
    ⟨(hKY.trans inf_le_left) hc.1, hc.2⟩
  refine exists_conjBy_of_bridge hinner hQ₁ hQ₂ hQ₃ hcX ?_ ?_
  · refine Subgroup.card_lt_of_lt
      (lt_of_le_of_ne (le_inf inf_le_left (hDle hQ₃)) fun heq => hv₁ ?_)
    exact (le_inf inf_le_left (hL₁S.trans hSQ₃)).trans heq.ge
  · refine Subgroup.card_lt_of_lt (lt_of_le_of_ne
      (le_inf (hDle (conjBy_mem_section7HStarFamily hcX.1 hcX.2 hQ₃)) inf_le_right)
      fun heq => hv₂ ?_)
    exact (le_inf (hL₂S.trans (conjBy_mono c hSQ₃)) inf_le_left).trans heq.ge

theorem transitivity_of_card_eq_of_prime {p : ℕ} [hp : Fact p.Prime] (T : Sylow p G)
    {V : Subgroup G} (hVT : V ≤ T) (hVZ : ∀ v ∈ V, ∀ y ∈ (T : Subgroup G), y * v = v * y)
    (hVcomm : IsMulCommutative V) (hVexp : ∀ x ∈ V, x ^ p = 1) (hVcard : p ^ 3 ≤ Nat.card V)
    (hsolv : ∀ v ∈ V, v ≠ 1 → Group.IsSolvable (Subgroup.centralizer ({v} : Set G)))
    {q : Nat.Primes} (hq : q.val ≠ p) (n : ℕ) :
    ∀ X : Subgroup G, Nat.card X = n → (T : Subgroup G) ≤ X →
      ConjugationActionTransitiveOn (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G))
        (section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hXn hTX
  have houter : ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Nat.card Y < Nat.card X →
      ConjugationActionTransitiveOn (Y ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G))
        (section7HStarFamily Y (T : Subgroup G) ({q} : Set Nat.Primes)) :=
    fun Y hTY hY => ih _ (hXn ▸ hY) Y rfl hTY
  have key : ∀ m : ℕ,
      ∀ Q₁ ∈ section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes),
      ∀ Q₂ ∈ section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes),
      Nat.card G - Nat.card (Q₁ ⊓ Q₂ : Subgroup G) = m →
        ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
          Q₂ = Q₁.conjBy (k : G) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro Q₁ hQ₁ Q₂ hQ₂ hm
    have hinner : ∀ R₁ ∈ section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes),
        ∀ R₂ ∈ section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes),
        Nat.card (Q₁ ⊓ Q₂ : Subgroup G) < Nat.card (R₁ ⊓ R₂ : Subgroup G) →
          ∃ k : (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) : Subgroup G),
            R₂ = R₁.conjBy (k : G) := fun R₁ hR₁ R₂ hR₂ hlt => ihm _ (by
      have := Subgroup.card_le_card_group (R₁ ⊓ R₂)
      omega) R₁ hR₁ R₂ hR₂ rfl
    by_cases h₁₂ : Q₁ ≤ Q₂
    · exact ⟨1, by rw [hQ₁.2 Q₂ h₁₂ hQ₂.1]; exact (Subgroup.conjBy_one Q₁).symm⟩
    by_cases h₂₁ : Q₂ ≤ Q₁
    · exact ⟨1, by rw [hQ₂.2 Q₁ h₂₁ hQ₁.1]; exact (Subgroup.conjBy_one Q₂).symm⟩
    by_cases hXD : X ≤ Subgroup.normalizer ((Q₁ ⊓ Q₂ : Subgroup G) : Set G)
    · exact exists_conjBy_of_le_normalizer_of_prime T hTX hVZ hVcomm hVexp hVcard hVT hsolv hq
        hinner hQ₁ hQ₂ h₁₂ h₂₁ hXD
    · exact exists_conjBy_of_not_le_normalizer hTX houter hinner hQ₁ hQ₂ h₁₂ h₂₁ hXD
  exact fun Q₁ hQ₁ Q₂ hQ₂ => key _ Q₁ hQ₁ Q₂ hQ₂ rfl

theorem thompson_transitivity_of_prime {p : ℕ} [hp : Fact p.Prime] (T : Sylow p G)
    {V : Subgroup G} (hVT : V ≤ T) (hVZ : ∀ v ∈ V, ∀ y ∈ (T : Subgroup G), y * v = v * y)
    (hVcomm : IsMulCommutative V) (hVexp : ∀ x ∈ V, x ^ p = 1) (hVcard : p ^ 3 ≤ Nat.card V)
    (hsolv : ∀ v ∈ V, v ≠ 1 → Group.IsSolvable (Subgroup.centralizer ({v} : Set G)))
    {q : Nat.Primes} (hq : q.val ≠ p) {X : Subgroup G} (hTX : (T : Subgroup G) ≤ X) :
    ConjugationActionTransitiveOn (X ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G))
      (section7HStarFamily X (T : Subgroup G) ({q} : Set Nat.Primes)) :=
  transitivity_of_card_eq_of_prime T hVT hVZ hVcomm hVexp hVcard hsolv hq _ X rfl hTX

end CFSG.Walter.JT
