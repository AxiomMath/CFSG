module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.SummaryAux3
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Sylow

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S34

section General

variable {G : Type u} [Group G]

theorem isMulCommutative_of_isDirectProduct [Finite G] {S : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) (hS : ∀ J ∈ S, IsMulCommutative J) : IsMulCommutative K := by
  refine isMulCommutative_iff.mpr fun x y => ?_
  obtain ⟨a, rfl⟩ := hK.equiv.surjective x
  obtain ⟨b, rfl⟩ := hK.equiv.surjective y
  rw [← map_mul, ← map_mul]
  congr 1
  funext J
  exact isMulCommutative_iff.mp (hS J.1 J.2) (a J) (b J)

theorem dvd_card_of_coprime_relIndex {r : ℕ} (hr : r.Prime) {P H : Subgroup G} (hPH : P ≤ H)
    (hidx : Nat.Coprime (P.relIndex H) r) (hrH : r ∣ Nat.card H) : r ∣ Nat.card P := by
  have h1 := Subgroup.card_mul_index (P.subgroupOf H)
  have h2 : Nat.card (P.subgroupOf H) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  rw [h2] at h1
  have h3 : r ∣ Nat.card P * P.relIndex H := h1 ▸ hrH
  rcases (Nat.Prime.dvd_mul hr).mp h3 with h | h
  · exact h
  · exact absurd h ((Nat.Prime.coprime_iff_not_dvd hr).mp hidx.symm)

end General

section Coord

variable {G : Type u} [Group G] [Finite G]

theorem IsDirectProduct.coord_congr {S S' : Set (Subgroup G)} (hS : S = S') {K : Subgroup G}
    (hK : IsDirectProduct S K) (hK' : IsDirectProduct S' K) {J : Subgroup G} (hJ : J ∈ S)
    (hJ' : J ∈ S') (x : ↥K) : ((hK.coord hJ x : J) : G) = ((hK'.coord hJ' x : J) : G) := by
  subst hS
  rfl

theorem eq_one_of_mem_kProd {p : ℕ} {A K : Subgroup G} (h : SemisimpleAction p A K) {r : ℕ}
    (hr : r.Prime) (hnd : ∀ J ∈ lcal K, ¬ r ∣ Nat.card (kJ A J)) {x : G} (hx : x ∈ kProd A K)
    {n : ℕ} (hxn : x ^ (r ^ n) = 1) : x = 1 := by
  obtain ⟨hxK, hc⟩ := h.mem_kProd_iff.mp hx
  have hD := h.isDirectProduct_lcal
  have hmem : x ∈ (⊥ : Subgroup G) := by
    refine hD.mem_of_coord_mem hxK fun J hJ => ?_
    have hy := hc J hJ
    have hyr : (hD.coord hJ ⟨x, hxK⟩) ^ (r ^ n) = 1 := by
      have : (⟨x, hxK⟩ : ↥K) ^ (r ^ n) = 1 := Subtype.ext hxn
      rw [← map_pow, this, map_one]
    have hyr' : ((hD.coord hJ ⟨x, hxK⟩ : J) : G) ^ (r ^ n) = 1 := by
      have := congrArg Subtype.val hyr
      simpa using this
    have hyK : (⟨((hD.coord hJ ⟨x, hxK⟩ : J) : G), hy⟩ : ↥(kJ A J)) ^ (r ^ n) = 1 :=
      Subtype.ext hyr'
    have h1 := orderOf_dvd_of_pow_eq_one hyK
    have h2 := orderOf_dvd_natCard (⟨((hD.coord hJ ⟨x, hxK⟩ : J) : G), hy⟩ : ↥(kJ A J))
    have hcop : Nat.Coprime (r ^ n) (Nat.card (kJ A J)) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hr).mpr (hnd J hJ))
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    have h4 := orderOf_eq_one_iff.mp h3
    have h5 : ((hD.coord hJ ⟨x, hxK⟩ : J) : G) = 1 := congrArg Subtype.val h4
    rw [h5]
    exact one_mem _
  exact Subgroup.mem_bot.mp hmem

end Coord

section Data

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {h : Counterexample p A θ} {E : Subgroup G} {f : G}

theorem Data.mem_kOf_of_pow
    (d : Data h E f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    {x : G} (hx : x ∈ θ f) {n : ℕ} (hxn : x ^ (r ^ n) = 1) : x ∈ kOf (θ f) := by
  obtain ⟨m, k, hmk⟩ := h.lemma616 d.zpowers_mem_rSetN_one x hx
  have hord : orderOf x ∣ r ^ n := orderOf_dvd_of_pow_eq_one hxn
  have hc2 : Nat.Coprime (r ^ n) (2 ^ m) :=
    Nat.Coprime.pow n m ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hc3 : Nat.Coprime (r ^ n) (3 ^ k) :=
    Nat.Coprime.pow n k ((Nat.coprime_primes hr Nat.prime_three).mpr hr3)
  have hcop : Nat.Coprime (orderOf x) (2 ^ m * 3 ^ k) :=
    Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.mul_right hc2 hc3)
  have hle : Subgroup.zpowers (x ^ (2 ^ m * 3 ^ k)) ≤ Subgroup.zpowers x :=
    Subgroup.zpowers_le.mpr (pow_mem (Subgroup.mem_zpowers x) _)
  have heq : Subgroup.zpowers (x ^ (2 ^ m * 3 ^ k)) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow hcop])
  have hx' : x ∈ Subgroup.zpowers (x ^ (2 ^ m * 3 ^ k)) := heq ▸ Subgroup.mem_zpowers x
  exact Subgroup.zpowers_le.mpr hmk hx'

theorem Data.thetaOf_sup (d : Data h E f) :
    thetaOf θ (E ⊔ Subgroup.zpowers f) = θ f ⊓ Subgroup.centralizer (E : Set G) := by
  have hθ := h.hyp.nearFunctor
  rw [sup_comm]
  exact (hθ.isFunctor.inf_centralizer_eq_thetaOf d.mem d.ne_one d.distE.mem.1).symm

variable {r : ℕ}

theorem Data.eq_one_of_centralizes
    (d : Data h E f) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hgood : ∀ L ∈ lcal (θ f), GoodComp p A θ E r L) {x : G} (hx : x ∈ θ f)
    (hxE : x ∈ Subgroup.centralizer (E : Set G)) {n : ℕ} (hxn : x ^ (r ^ n) = 1) : x = 1 := by
  have hxK : x ∈ kOf (θ f) := d.mem_kOf_of_pow hr hr2 hr3 hx hxn
  have hK := d.semisimpleAction
  have hxk : x ∈ kProd A (kOf (θ f)) := by
    refine hK.mem_kProd_iff.mpr ⟨hxK, fun J hJ => ?_⟩
    have hJ' : J ∈ lcal (θ f) := d.lcal_kOf ▸ hJ
    rw [IsDirectProduct.coord_congr d.lcal_kOf hK.isDirectProduct_lcal d.isDirectProduct hJ hJ']
    exact hK.cenIn_norIn_le_kJ hJ (d.coord_mem_cenIn hJ' hxK hxE)
  exact eq_one_of_mem_kProd hK hr (fun J hJ => (hgood J (d.lcal_kOf ▸ hJ)).not_dvd) hxk hxn

theorem Data.eq_one_of_mem_ssol
    (d : Data h E f) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hgood : ∀ L ∈ lcal (θ f), GoodComp p A θ E r L) {x : G} (hx : x ∈ θ f)
    (hxS : x ∈ ssol p A θ) {n : ℕ} (hxn : x ^ (r ^ n) = 1) : x = 1 := by
  have hxK : x ∈ kOf (θ f) := d.mem_kOf_of_pow hr hr2 hr3 hx hxn
  have hxk : x ∈ kProd A (kOf (θ f)) := d.kProd_eq ▸ ⟨hxS, hxK⟩
  exact eq_one_of_mem_kProd d.semisimpleAction hr
    (fun J hJ => (hgood J (d.lcal_kOf ▸ hJ)).not_dvd) hxk hxn

theorem Data.not_mem_of_mem_plane (d : Data h E f) {e : G} (he : e ∈ A)
    (hen : e ∉ E ⊔ Subgroup.zpowers f) {b : G}
    (hb : b ∈ Subgroup.zpowers f ⊔ Subgroup.zpowers e) (hb1 : b ≠ 1) : b ∉ E := by
  intro hbE
  have hθ := h.hyp.nearFunctor
  have hcE : Nat.card E = p := by rw [d.distE.mem.2, pow_one]
  have hzb : Nat.card (Subgroup.zpowers b) = p :=
    Sec6Gen.card_zpowers_of_pow_eq_one hθ.prime (hθ.elemAbelian.2 b (d.distE.mem.1 hbE)) hb1
  have hEq : Subgroup.zpowers b = E :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbE) (by rw [hcE, hzb])
  have hEB : E ≤ Subgroup.zpowers f ⊔ Subgroup.zpowers e :=
    hEq ▸ Subgroup.zpowers_le.mpr hb
  have hle : E ⊔ Subgroup.zpowers f ≤ Subgroup.zpowers f ⊔ Subgroup.zpowers e :=
    _root_.sup_le hEB le_sup_left
  have hEF : E ⊔ Subgroup.zpowers f = Subgroup.zpowers f ⊔ Subgroup.zpowers e :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [d.card_plane he hen, d.card_sup])
  exact hen (hEF ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e))

end Data

section Sr

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_srSubgroup (h : Counterexample p A θ) (r : ℕ) :
    ∃ V : Subgroup G, Maximal (fun X => X ∈ assoc p A θ ∧ IsPGroup r X) V := by
  have hθ := h.hyp.nearFunctor
  have hbot : (⊥ : Subgroup G) ∈ assoc p A θ := by
    refine mem_assoc_of_le hθ.prime (dsub_mem_assoc hθ) bot_le ?_
    show A ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G)
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨V, -, hV⟩ := Finite.exists_le_maximal
    (p := fun X : Subgroup G => X ∈ assoc p A θ ∧ IsPGroup r X) (a := ⊥) ⟨hbot, IsPGroup.of_bot⟩
  exact ⟨V, hV⟩

theorem sylow_of_maximal (h : Counterexample p A θ) {r : ℕ} (hr : r.Prime) (hrp : r ≠ p)
    {V : Subgroup G} (hV : Maximal (fun X => X ∈ assoc p A θ ∧ IsPGroup r X) V) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) :
    cenIn V {a} ≤ θ a ∧ IsPGroup r (cenIn V {a}) ∧
      Nat.Coprime ((cenIn V {a}).relIndex (θ a)) r := by
  have hθ := h.hyp.nearFunctor
  have hS : IsSrSubgroup p A θ (NearASolvable p A) r V := hV
  have : Fact r.Prime := ⟨hr⟩
  have hPr : ∀ X : Subgroup G, IsPGroup r X → NearASolvable p A X := by
    intro X hX
    have : Group.IsNilpotent ↥X := hX.isNilpotent
    refine nearASolvable_of_isSolvable inferInstance ?_
    obtain ⟨k, hk⟩ := hX.exists_card_eq
    rw [hk]
    exact ((Nat.coprime_primes hθ.prime hr).mpr hrp.symm).pow_right k
  have h1 := hS.isSrSubgroupOf_inf_centralizer h.hyp.prime h.hyp.elemAbelian h.hyp.card.ge
    h.hyp.isFunctor hr hrp hPr ha ha1
  exact Nonsolv.isSylow_of_isSrSubgroupOf h.hyp.prime hr hrp h.hyp.elemAbelian
    (hθ.isFunctor.normalized a ha ha1) (hθ.isFunctor.coprime a ha ha1) h1

section SrData

variable {h : Counterexample p A θ} {E : Subgroup G} {r : ℕ} {V : Subgroup G} {f : G}

structure SrData (h : Counterexample p A θ) (E : Subgroup G) (r : ℕ) (V : Subgroup G) : Prop where
  distE : DistE p A θ E
  prime : r.Prime
  ne_p : r ≠ p
  ne_two : r ≠ 2
  ne_three : r ≠ 3
  good : ∀ f : G, Data h E f → ∀ L ∈ lcal (θ f), GoodComp p A θ E r L
  maximal : Maximal (fun X => X ∈ assoc p A θ ∧ IsPGroup r X) V

theorem SrData.mem_assoc (s : SrData h E r V) : V ∈ assoc p A θ := s.maximal.1.1

theorem SrData.isPGroup (s : SrData h E r V) : IsPGroup r V := s.maximal.1.2

theorem SrData.pow_eq_one (s : SrData h E r V) {x : G} (hx : x ∈ V) :
    ∃ n : ℕ, x ^ (r ^ n) = 1 := by
  obtain ⟨n, hn⟩ := s.isPGroup ⟨x, hx⟩
  exact ⟨n, congrArg Subtype.val hn⟩

theorem SrData.sylow (s : SrData h E r V) (d : Data h E f) :
    cenIn V {f} ≤ θ f ∧ IsPGroup r (cenIn V {f}) ∧
      Nat.Coprime ((cenIn V {f}).relIndex (θ f)) r :=
  sylow_of_maximal h s.prime s.ne_p s.maximal d.mem d.ne_one

theorem SrData.cenIn_le_kOf
    (s : SrData h E r V) (d : Data h E f) : cenIn V {f} ≤ kOf (θ f) := by
  intro x hx
  obtain ⟨n, hn⟩ := s.pow_eq_one hx.1
  exact d.mem_kOf_of_pow s.prime s.ne_two s.ne_three ((s.sylow d).1 hx) hn

theorem SrData.dvd_card
    (s : SrData h E r V) (d : Data h E f) : r ∣ Nat.card (θ f) := by
  obtain ⟨L, hL⟩ := d.lcal_nonempty
  exact ((s.good f d L hL).dvd).trans (Subgroup.card_dvd_of_le (lcal_le hL))

theorem SrData.ne_bot
    (s : SrData h E r V) (d : Data h E f) : cenIn V {f} ≠ ⊥ := by
  intro hbot
  have hdvd := dvd_card_of_coprime_relIndex s.prime (s.sylow d).1 (s.sylow d).2.2 (s.dvd_card d)
  rw [hbot, Subgroup.card_bot] at hdvd
  exact s.prime.one_lt.ne' (Nat.dvd_one.mp hdvd)

theorem SrData.inf_thetaOf
    (s : SrData h E r V) : V ⊓ thetaOf θ E = ⊥ := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨f₀, hf₀A, hf₀E⟩ := exists_mem_not_mem h s.distE
  have d₀ : Data h E f₀ := ⟨s.distE, hf₀A, hf₀E⟩
  obtain ⟨e, he, hen⟩ := d₀.exists_mem_sdiff
  have hBA : Subgroup.zpowers f₀ ⊔ Subgroup.zpowers e ≤ A := d₀.plane_le he
  have hB2 : p ^ 2 ≤ Nat.card (Subgroup.zpowers f₀ ⊔ Subgroup.zpowers e : Subgroup G) :=
    (d₀.card_plane he hen).ge
  have hBe : IsElemAbelian p (Subgroup.zpowers f₀ ⊔ Subgroup.zpowers e : Subgroup G) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p h.hyp.elemAbelian hBA
  have hVA : A ≤ Subgroup.normalizer (V : Set G) := s.mem_assoc.1
  have hEA : A ≤ Subgroup.normalizer (thetaOf θ E : Set G) :=
    hθ.isFunctor.normalizes_thetaOf s.distE.mem.1
  have hQ : Subgroup.zpowers f₀ ⊔ Subgroup.zpowers e ≤
      Subgroup.normalizer ((V ⊓ thetaOf θ E : Subgroup G) : Set G) :=
    hBA.trans (Admits.inf hVA hEA)
  have hQcop : Nat.Coprime p (Nat.card ↥(V ⊓ thetaOf θ E)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) s.mem_assoc.2.1
  have hgen := iSup_inf_centralizer h.hyp.prime hBe hB2 hQ hQcop
  refine le_antisymm ?_ bot_le
  rw [← hgen]
  refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
  rintro x ⟨⟨hxV, hxE⟩, hxb⟩
  have hbA : b ∈ A := hBA hb
  have hbE : b ∉ E := d₀.not_mem_of_mem_plane he hen hb hb1
  have db : Data h E b := ⟨s.distE, hbA, hbE⟩
  have hxθ : x ∈ θ b := s.mem_assoc.2.2.1 b hbA hb1 ⟨hxV, hxb⟩
  have hxC : x ∈ Subgroup.centralizer (E : Set G) :=
    hθ.isFunctor.thetaOf_le_centralizer s.distE.mem.1 hxE
  obtain ⟨n, hn⟩ := s.pow_eq_one hxV
  exact Subgroup.mem_bot.mpr
    (db.eq_one_of_centralizes s.prime s.ne_two s.ne_three (s.good b db) hxθ hxC hn)

theorem SrData.isMulCommutative
    (s : SrData h E r V) : IsMulCommutative V := by
  have hθ := h.hyp.nearFunctor
  refine isMulCommutative_of_centralizers h.hyp.prime h.hyp.elemAbelian h.hyp.card.ge
    s.mem_assoc.1 s.mem_assoc.2.1 fun a ha ha1 => ?_
  by_cases haE : a ∈ E
  · have hcard : Nat.card (Subgroup.zpowers a) = p :=
      Sec6Gen.card_zpowers_of_pow_eq_one hθ.prime (hθ.elemAbelian.2 a ha) ha1
    have hcE : Nat.card E = p := by rw [s.distE.mem.2, pow_one]
    have hEq : Subgroup.zpowers a = E :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haE) (by rw [hcE, hcard])
    have hθa : θ a = thetaOf θ E := by
      rw [← hEq]
      exact (hθ.isFunctor.thetaOf_zpowers ha ha1).symm
    have hle : cenIn V {a} ≤ V ⊓ thetaOf θ E := fun x hx =>
      ⟨hx.1, hθa ▸ s.mem_assoc.2.2.1 a ha ha1 hx⟩
    have hbot : cenIn V {a} = ⊥ := le_bot_iff.mp (s.inf_thetaOf ▸ hle)
    rw [hbot]
    exact isMulCommutative_iff.mpr fun x y => by rw [Subsingleton.elim x y]
  · have d : Data h E a := ⟨s.distE, ha, haE⟩
    obtain ⟨-, hP, hidx⟩ := s.sylow d
    have hPK := s.cenIn_le_kOf d
    have hidxK : Nat.Coprime ((cenIn V {a}).relIndex (kOf (θ a))) r :=
      Nat.Coprime.coprime_dvd_left
        (Dvd.intro _ (Subgroup.relIndex_mul_relIndex (cenIn V {a}) (kOf (θ a)) (θ a) hPK
          (kOf_le (θ a)))) hidx
    obtain ⟨hdp, hcop⟩ :=
      Nonsolv.IsDirectProduct.sylow_decomp d.isDirectProduct s.prime hPK hP hidxK
    refine isMulCommutative_of_isDirectProduct hdp ?_
    rintro _ ⟨L, hL, rfl⟩
    exact (s.good a d L hL).abelian _ inf_le_right hP.to_inf_left (hcop L hL)

theorem SrData.not_le_ssol
    (s : SrData h E r V) (d : Data h E f) : ¬ V ≤ ssol p A θ := by
  intro hVS
  have hPr := s.sylow d
  have : Fact r.Prime := ⟨s.prime⟩
  have hdvd : r ∣ Nat.card (cenIn V {f}) :=
    dvd_card_of_coprime_relIndex s.prime hPr.1 hPr.2.2 (s.dvd_card d)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(cenIn V {f})) r hdvd
  have hxo : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
  have hxθ : (x : G) ∈ θ f := hPr.1 x.2
  have hxS : (x : G) ∈ ssol p A θ := hVS x.2.1
  have hxn : (x : G) ^ (r ^ 1) = 1 := by
    rw [pow_one, ← hxo]
    exact pow_orderOf_eq_one _
  have h1 := d.eq_one_of_mem_ssol s.prime s.ne_two s.ne_three (s.good f d) hxθ hxS hxn
  rw [h1, orderOf_one] at hxo
  exact s.prime.one_lt.ne hxo

theorem SrData.sup_eq
    (s : SrData h E r V) (d : Data h E f) :
    cenIn V {f} ⊔ (thetaOf θ (E ⊔ Subgroup.zpowers f) ⊓ sThree p A θ) = kOf (θ f) := by
  have hθ := h.hyp.nearFunctor
  have hPr := s.sylow d
  have hPK := s.cenIn_le_kOf d
  have hT : thetaOf θ (E ⊔ Subgroup.zpowers f) ⊓ sThree p A θ ≤ kOf (θ f) := by
    rw [d.thetaOf_sup]
    exact fun x hx => (d.sThree_inf_le ⟨hx.2, hx.1.1⟩).2
  refine le_antisymm (_root_.sup_le hPK hT) ?_
  have hidxK : Nat.Coprime ((cenIn V {f}).relIndex (kOf (θ f))) r :=
    Nat.Coprime.coprime_dvd_left
      (Dvd.intro _ (Subgroup.relIndex_mul_relIndex (cenIn V {f}) (kOf (θ f)) (θ f) hPK
        (kOf_le (θ f)))) hPr.2.2
  obtain ⟨-, hcop⟩ :=
    Nonsolv.IsDirectProduct.sylow_decomp d.isDirectProduct s.prime hPK hPr.2.1 hidxK
  rw [← d.isDirectProduct.sSup_eq]
  refine sSup_le fun L hL => ?_
  have hLθ : L ≤ θ f := lcal_le hL
  have hPL : r ∣ Nat.card ↥(cenIn V {f} ⊓ L) :=
    dvd_card_of_coprime_relIndex s.prime inf_le_right (hcop L hL) (s.good f d L hL).dvd
  have : Fact r.Prime := ⟨s.prime⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(cenIn V {f} ⊓ L)) r hPL
  have hY := (s.good f d L hL).generate
    ((cenIn V {f} ⊔ (thetaOf θ (E ⊔ Subgroup.zpowers f) ⊓ sThree p A θ)) ⊓ L) inf_le_right
    (fun x hx => ⟨Subgroup.mem_sup_right ⟨?_, hx.1.2⟩, hx.1.1⟩)
    ⟨(y : G), ⟨Subgroup.mem_sup_left y.2.1, y.2.2⟩, by rw [Subgroup.orderOf_coe]; exact hy⟩
  · exact (inf_eq_right.mp hY)
  · rw [d.thetaOf_sup]
    exact ⟨hLθ hx.1.1, hθ.isFunctor.thetaOf_le_centralizer s.distE.mem.1 hx.2⟩

end SrData

end Sr

end Sec6S34

end CFSG.SignalizerFunctorTheorem.McBride.Near
